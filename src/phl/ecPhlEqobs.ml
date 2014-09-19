(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcPath
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
(* Remark: for the adversary case we assume that inv do not contain
 * the equality of glob *)
let mk_inv_spec (_pf : proofenv) env inv fl fr =
  match NormMp.is_abstract_fun fl env with
  | true ->
    let (topl, _, oil, sigl),
      (topr, _, _  , sigr) = EcLowPhlGoal.abstract_info2 env fl fr in
    let eqglob = f_eqglob topl mleft topr mright in
    let lpre = if oil.oi_in then [eqglob;inv] else [inv] in
    let eq_params =
      f_eqparams
        fl sigl.fs_arg sigl.fs_anames mleft
        fr sigr.fs_arg sigr.fs_anames mright in
    let eq_res = f_eqres fl sigl.fs_ret mleft fr sigr.fs_ret mright in
    let pre    = f_ands (eq_params::lpre) in
    let post   = f_ands [eq_res; eqglob; inv] in
      f_equivF pre fl fr post

  | false ->
      let defl = EcEnv.Fun.by_xpath fl env in
      let defr = EcEnv.Fun.by_xpath fr env in
      let sigl, sigr = defl.f_sig, defr.f_sig in
      let testty =
           EcReduction.EqTest.for_type env sigl.fs_arg sigr.fs_arg
        && EcReduction.EqTest.for_type env sigl.fs_ret sigr.fs_ret
      in

      if not testty then raise EqObsInError;
      let eq_params =
        f_eqparams
          fl sigl.fs_arg sigl.fs_anames mleft
          fr sigr.fs_arg sigr.fs_anames mright in
      let eq_res = f_eqres fl sigl.fs_ret mleft fr sigr.fs_ret mright in
      let pre = f_and eq_params inv in
      let post = f_and eq_res inv in
        f_equivF pre fl fr post

(* -------------------------------------------------------------------- *)
type eqobs_in_rec_info =
  | EORI_adv of Mpv2.t
  | EORI_fun of Mpv2.t
  | EORI_unknown of EcIdent.t option

type eqobs_in_log = {
  query    : ((xpath * xpath * Mpv2.t) * (Mpv2.t * form)) list;
  forproof : eqobs_in_rec_info Mf.t ;
}

(* -------------------------------------------------------------------- *)
let find_eqobs_in_log log fl fr eqo =
  let test ((fl',fr',eqo'), _) =
    EcPath.x_equal fl fl' && EcPath.x_equal fr fr' && Mpv2.equal eqo eqo' in
  try Some (snd (List.find test log.query)) with Not_found -> None

(* -------------------------------------------------------------------- *)
let add_eqobs_in_log fl fr eqo (eqi,spec,info) log =
  { query = ((fl,fr,eqo), (eqi,spec)) :: log.query;
    forproof = Mf.add spec info log.forproof }

(* -------------------------------------------------------------------- *)
let extend_body f fsig body =
  let arg = pv_arg f in
  let i =
    match fsig.fs_anames with
    | None | Some [] -> []

    | Some [v] ->
        [i_asgn (LvVar (pv_loc f v.v_name, v.v_type),
                 e_var arg fsig.fs_arg)]

    | Some lv ->
        let lv = List.map (fun v -> pv_loc f v.v_name, v.v_type) lv in
        [i_asgn (LvTuple lv, e_var arg fsig.fs_arg)]

  in
    (arg, s_seq (stmt i) body)

(* -------------------------------------------------------------------- *)
let t_eqobs_inS_r finfo eqo inv tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let es = tc1_as_equivS tc in
  let ml, mr = fst es.es_ml, fst es.es_mr in

  (* TODO check that inv contains only global *)
  let ifvl = PV.fv env ml inv in
  let ifvr = PV.fv env mr inv in

  let sl,sr,(_,sg),eqi =
    EcPV.eqobs_in env finfo () es.es_sl es.es_sr eqo (ifvl, ifvr) in

  let post = Mpv2.to_form ml mr eqo inv in
  let pre  = Mpv2.to_form ml mr eqi inv in

  if not (EcReduction.is_alpha_eq hyps post es.es_po) then
    tc_error !!tc "cannot apply eqobs_in";

  let concl = f_equivS es.es_ml es.es_mr es.es_pr sl sr pre in

  FApi.xmutate1 tc `EqobsIn (sg @ [concl])

let t_eqobs_inS = FApi.t_low3 "eqobs-in" t_eqobs_inS_r

(* -------------------------------------------------------------------- *)
let rec eqobs_inF pf env eqg (inv, ifvl, ifvr as inve) log fl fr eqO =
  match find_eqobs_in_log log fl fr eqO with
  | Some (eqi, spec) -> (log, eqi, spec)
  | None ->
    let nfl  = NormMp.norm_xfun env fl in
    let nfr  = NormMp.norm_xfun env fr in
    let defl = Fun.by_xpath nfl env in
    let defr = Fun.by_xpath nfr env in

    match defl.f_def, defr.f_def with
    | FBabs oil, FBabs oir -> begin
        let top = EcPath.m_functor nfl.EcPath.x_top in
        let log, ieqg =
          try (* Try to infer the good invariant for oracle *)
            let eqo = Mpv2.remove_glob top eqO in
            let rec aux eqo =
              let log, eqi =
                List.fold_left2
                  (fun (log,eqo) o_l o_r ->
                    let log, eqo, _ = eqobs_inF pf env eqg inve log o_l o_r eqo in
                    log, eqo)
                  (log,eqo) oil.oi_calls oir.oi_calls in
              if Mpv2.subset eqi eqo then log, eqo else aux eqi in
            aux eqo
          with EqObsInError ->
            if not (Mpv2.subset eqO eqg) then raise EqObsInError;
            (log, Mpv2.remove_glob top eqg) in

        let peqg = if oil.oi_in then Mpv2.add_glob env top top ieqg else ieqg in
        let inv  = Mpv2.to_form mleft mright ieqg inv in
        let spec = mk_inv_spec pf env inv fl fr in
        let log  = add_eqobs_in_log fl fr eqO (peqg,spec, EORI_adv ieqg) log in
        (log, peqg, spec)
    end

    | FBdef funl, FBdef funr -> begin
        try
          let sigl, sigr = defl.f_sig, defr.f_sig in
          let testty =
               EcReduction.EqTest.for_type env sigl.fs_arg sigr.fs_arg
            && EcReduction.EqTest.for_type env sigl.fs_ret sigr.fs_ret
          in
          if not testty then raise EqObsInError;
          let eqo' =
            match funl.f_ret, funr.f_ret with
            | None, None -> eqO
            | Some el, Some er -> add_eqs env eqO el er
            | _, _ -> raise EqObsInError in

          let argl, bodyl = extend_body nfl sigl funl.f_body in
          let argr, bodyr = extend_body nfr sigr funr.f_body in
          let sl, sr, (log,_), eqi =
            eqobs_in env
              (eqobs_inF pf env eqg inve)
              log bodyl bodyr eqo' (ifvl,ifvr) in

          if sl.s_node <> [] || sr.s_node <> [] then
            raise EqObsInError;

          let geqi = Mpv2.remove env argl argr eqi in
          Mpv2.check_glob geqi;
          let eq_params =
            f_eqparams
              fl sigl.fs_arg sigl.fs_anames mleft
              fr sigr.fs_arg sigr.fs_anames mright in
          let eq_res = f_eqres fl sigl.fs_ret mleft fr sigr.fs_ret mright in
          let pre    = f_and eq_params (Mpv2.to_form mleft mright geqi inv) in
          let post   = f_and eq_res (Mpv2.to_form mleft mright eqO inv) in
          let spec   = f_equivF pre fl fr post in
          let log    = add_eqobs_in_log fl fr eqO (geqi, spec, EORI_fun eqo') log in
          (log, geqi, spec)

        with EqObsInError ->
          if not (Mpv2.subset eqO eqg) then raise EqObsInError;
          let inv  = Mpv2.to_form mleft mright eqg inv in
          let spec = mk_inv_spec pf env inv fl fr in
          let log  = add_eqobs_in_log fl fr eqO (eqg,spec,EORI_unknown None) log in
          (log, eqg, spec)
      end

    | _, _ -> raise EqObsInError

(* -------------------------------------------------------------------- *)
let tc_process_prhl_post tc phi =
  let env, hyps, concl = FApi.tc1_eflat tc in
  let (ml, mr) =
    match concl.f_node with
    | FequivS es -> (es.es_ml, es.es_mr)
    | FequivF ef -> snd (EcEnv.Fun.equivF_memenv ef.ef_fl ef.ef_fr env)
    | _          -> assert false
  in
  let hyps = LDecl.push_all [ml; mr] hyps in
  TTC.pf_process_form !!tc hyps tbool phi

(* -------------------------------------------------------------------- *)
let process_eqobs_in (geq', ginv, eqs') tc =
  let env, hyps, concl = FApi.tc1_eflat tc in
  let ienv = LDecl.inv_memenv hyps in

  let isfun, ml, mr, post =
    match concl.f_node with
    | FequivS es ->
        (`Stmt (es.es_sl, es.es_sr), fst es.es_ml, fst es.es_mr, es.es_po)
    | FequivF ef ->
        (`Fun (ef.ef_fl, ef.ef_fr), mleft, mright, ef.ef_po)
    | _ -> tc_error !!tc "the conclusion does not end with a prhl judgment"
  in

  let toeq ml mr f =
    try EcPV.Mpv2.of_form env ml mr f
    with _ ->
      tc_error_lazy !!tc (fun fmt ->
        let ppe = EcPrinting.PPEnv.ofenv env in
        Format.fprintf fmt
          "cannot recognize %a as a set of equalities"
          (EcPrinting.pp_form ppe) f)
  in

  let geq =
    match geq' with
    | None -> toeq mleft mright f_true
    | Some geq' ->
      let geq = TTC.pf_process_form !!tc ienv tbool geq' in
      reloc geq'.pl_loc (toeq mleft mright) geq in

  let ginv = ginv |> omap (TTC.pf_process_form !!tc ienv tbool) |> odfl f_true in
  let ifvl = EcPV.PV.fv env ml ginv in
  let ifvr = EcPV.PV.fv env mr ginv in

  let eqs =
    match eqs' with
    | None -> begin
        try EcPV.Mpv2.needed_eq env ml mr post
        with _ -> tc_error !!tc "cannot infer the set of equalities"
      end
    | Some eqs' ->
      let eqs = tc_process_prhl_post tc eqs' in
      reloc eqs'.pl_loc (toeq ml mr) eqs in

  let log, eqO =
    match isfun with
    | `Stmt(sl,sr) ->
      let _, _, (log,_), _ =
        EcPV.eqobs_in env
          (eqobs_inF !!tc env geq (ginv,ifvl,ifvr))
          { query = []; forproof = Mf.empty; }
          sl sr eqs (ifvl,ifvr) in 
      log, eqs

    | `Fun(fl,fr) ->
      let eqO = (Mpv2.remove env (pv_res fl) (pv_res fr) eqs) in
      let log = proj3_1 (
        eqobs_inF
          !!tc env geq (ginv,ifvl,ifvr)
          { query = []; forproof = Mf.empty } fl fr eqO) in
      (log, eqO)
  in

  let onF _ fl fr eqo =
    let (eqo, spec) = oget (find_eqobs_in_log log fl fr eqo) in
    (), eqo, spec
  in

  let t_eqobs eqs tc =
    let es = tc1_as_equivS tc in
    let ml, mr = fst es.es_ml, fst es.es_mr in
    let post = EcPV.Mpv2.to_form ml mr eqs ginv in
    let pre  = es.es_pr in
      FApi.t_seqsub
        (EcPhlConseq.t_equivS_conseq pre post)
        [t_logic_trivial;
         t_logic_trivial;
         (fun tc ->
           FApi.t_last
             (FApi.t_try (FApi.t_seq EcPhlSkip.t_skip t_logic_trivial))
             (t_eqobs_inS onF eqs ginv tc))]
        tc
  in

  let tocut =
    Mf.fold (fun spec eori l ->
      match eori with
      | EORI_unknown None -> spec :: l
      | _ -> l) log.forproof [] in

  let forproof = ref log.forproof in

  let rec t_cut_spec l tc =
    match l with
    | [] -> t_id tc
    | spec :: l ->
      let hyps = FApi.tc1_hyps tc in
      let id   = LDecl.fresh_id hyps "H" in
        forproof := Mf.add spec (EORI_unknown (Some id)) !forproof;
        FApi.t_seqsub (t_cut spec)
          [t_id; FApi.t_seq (t_intros_i [id]) (t_cut_spec l)]
          tc
  in

  let t_rec tc =
    let concl = FApi.tc1_goal tc in
    match Mf.find_opt concl !forproof with
    | Some (EORI_adv geq) ->
      let tc =
        EcPhlFun.t_equivF_abs
          (EcPV.Mpv2.to_form mleft mright geq ginv) tc
      in
        FApi.t_firsts t_logic_trivial 2 tc

    | Some (EORI_fun eqs) ->
        FApi.t_seq EcPhlFun.t_equivF_fun_def (t_eqobs eqs) tc

    | Some (EORI_unknown (Some id)) -> t_apply_hyp id tc

    | _ -> t_fail tc
  in

  let t_last tc =
    match isfun with
    | `Fun (fl,fr) ->
      let spec = proj3_3 (onF () fl fr eqO) in
      let ef   = pf_as_equivF !!tc spec in
      FApi.t_seqsub
        (EcPhlConseq.t_equivF_conseq ef.ef_pr ef.ef_po)
        [t_logic_trivial;
         t_logic_trivial;
         FApi.t_repeat t_rec] tc

    | _ -> FApi.t_seq (t_eqobs eqs) (FApi.t_repeat t_rec) tc
  in

  FApi.t_last t_last (t_cut_spec tocut tc)
