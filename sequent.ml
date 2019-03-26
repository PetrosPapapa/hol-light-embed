(* ========================================================================= *)
(* Object level reasoning for sequent calculus-style, propositional embedded *)
(* logics using meta-level natural deduction.                                *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                 2009-2017                                 *)
(* ========================================================================= *)

(* Dependencies *)

needs "IsabelleLight/make.ml";;

needs "tools/make.ml";;
needs "tools/Library/multisets.ml";;

(* ------------------------------------------------------------------------- *)
(* Embedded interactive prover.                                              *)
(* ------------------------------------------------------------------------- *)
(* This is built in the style of Isabelle Light.                             *)
(* However, it is designed to work for the embedded logic.                   *)
(* ------------------------------------------------------------------------- *)
(* - This means that we need to take care of multisets when matching.        *)
(* - We are also taking care of type theory term construction using          *)
(* metavariables. Since we are using unification, construction works both    *)
(* when proving backwards and forwards.                                      *)
(* - When proving backwards, it makes sense to define a goal of the form:    *)
(*   ? P . |-- (...) P                                                       *)
(* Then using META_EXISTS_TAC will convert P into a meta-variable that can   *)
(* be constructed during the backwards proof.                                *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Embedded logics are expected to have an (inductively?) defined relation   *)
(* for logical consequence (turnstile). Depending on the embedded logic,     *)
(* this can have the following types of arguments:                           *)
(* - Static terms (e.g. single conclusion intuitionistic logic)              *)
(* - Multisets of terms (e.g. assumptions in sequents)                       *)
(* - Construction terms (type theory translations)                           *)
(* The matching algorithm tries to use multiset matching for all arguments   *)
(* or else term matching or else term unification.                           *)
(* ------------------------------------------------------------------------- *)

let split_seq tm =
  let comb,args = strip_comb tm in
  (fst o dest_const) comb,args;;


(* ------------------------------------------------------------------------- *)
(* A function used in the justification of our rule tactics.                 *)
(* Discharges a list of terms dischl from theorem thm after instantiating    *)
(* both with i.                                                              *)
(* ------------------------------------------------------------------------- *)

let dischi_pair = 
  fun i (dischl,thm) -> 
    DISCHL (map (instantiate i) dischl) (INSTANTIATE_ALL i thm);;


(* ------------------------------------------------------------------------- *)
(* Try to match terms. If that fails, try to unify them.                     *)
(* ------------------------------------------------------------------------- *)
(* Unification only allows instantiations of metavariables. This means the   *)
(* term matching attempt may be redundant. However, term matching is higher  *)
(* order, so we are keeping it around for now.                               *)
(* ------------------------------------------------------------------------- *)

let term_matchOrUnify avoids metas l r = 
  try ( term_match avoids l r )
    with Failure _ -> 
           try ( term_unify metas l r ) 
           with Failure _ -> failwith ("term_matchOrUnify: " ^ (string_of_term l) ^ " =/= " ^ (string_of_term r)) ;;

(* Advanced multiset matching. *)
    
let munion_match =
  fun avoids metas rl gl ->
    let prop_ty = try ( (hd o snd o dest_type o type_of) gl )
      with Failure _ -> failwith "munion_match: invalid type" in
    
    let gargs = flat_munion gl 
    and rargs = flat_munion rl in
    let is_mset_var = fun x -> (is_var x) && not (mem x avoids) in

    let rargs_var,rargs_nonvar = partition is_mset_var rargs in

    (* Remove things that already match to avoid weird chain matches of channels *)
    let rargs_nonvar,gargs = remove_common_once rargs_nonvar gargs in
    
    (* First we try to match nonvariable assumptions since they need to match directly *)
    let ins = match_list (term_matchOrUnify avoids metas) rargs_nonvar gargs in 

    (* Apply the instantiations that we've found so far *)
    let rargs_var_new = map (instantiate ins) rargs_var
    and rargs_nonvar_new = map (instantiate ins) rargs_nonvar in

    (* Filter all the remaining assumptions that need to be matched *)
    let gargs_rest = remove_list gargs rargs_nonvar_new in

    (* Instantiate mempty with the appropriate type. *)
    let mempty = inst [prop_ty,`:A`] `mempty:(A)multiset` in

    (* Make sure all remaining rule assumptions get a pair and no goal assumptions remain *)
    let gargs_rest = adjust_munion_list_length mempty (length rargs_var_new) gargs_rest in

    (* Pair them up *)
    let pairs = zip rargs_var_new gargs_rest in

    let insts = map (fun x,y -> term_match avoids x y) pairs in
      itlist compose_insts insts ins;;





(* ------------------------------------------------------------------------- *)
(* Matching of 2 sequents.                                                   *)
(* ------------------------------------------------------------------------- *)

let seq_match = 
  fun avoids metas rl gl ->
  try (
    let gcomb,gargs = strip_comb gl
    and rcomb,rargs = strip_comb rl in

    let cinst = try ( term_match [] rcomb gcomb )
    with Failure _ -> failwith "Sequent operators (turnstiles) don't match." in
    
    let mset_match i (r,g) =
      let ri,gi = (instantiate i r),(instantiate i g) in
      let res = try ( munion_match avoids metas ri gi )
		      	  (* munion_match error reporting is more informative in most cases *)
	with Failure s -> (try ( term_matchOrUnify avoids metas ri gi ) with Failure _ -> failwith s) in
      compose_insts i res in

    List.fold_left mset_match null_inst (zip rargs gargs)
  ) with Failure s -> failwith ("seq_match: " ^ s);;
 


let seq_eq lh rh = 
  try (
    let lcomb,largs = split_seq lh
    and rcomb,rargs = split_seq rh in

    lcomb = rcomb &&
	forall (fun x,y -> multiset_is_eq x y) (zip largs rargs)
  ) with Failure _ -> lh = rh;;



(* ------------------------------------------------------------------------- *)
(* Version of PROVE_HYP that matches multisets.                              *)
(* ------------------------------------------------------------------------- *)

let MSET_PROVE_HYP ath bth =
  try (
    let hyps = map (snd o strip_forall) (hyp bth)
    and con = (snd o strip_forall o concl) ath in
    match List.find_opt (fun x -> seq_eq con x) hyps with
      None -> bth 
      | Some(mhyp) ->
    let eq = PROVE_MULTISET_EQ (concl ath) mhyp in
    let ath' = EQ_MP eq ath in
    EQ_MP (DEDUCT_ANTISYM_RULE ath' bth) ath'
  ) with Failure s -> print_string ("ATH: " ^ (string_of_thm ath) ^ "\nBTH: " ^ (string_of_thm bth) ^"\n"); failwith ("MSET_PROVE_HYP: " ^ s);;  

let NORM_MSET_INST_ALL i thm = (NORMALIZE_MULTISET_ALL o INSTANTIATE_ALL i) thm;;


(* ------------------------------------------------------------------------- *)
(* PART_MATCH I using the sequent matcher and also returning the inst.       *)
(* ------------------------------------------------------------------------- *)

(*
let PART_SEQMATCH_I =
  let rec match_bvs t1 t2 acc =
    try let v1,b1 = dest_abs t1
        and v2,b2 = dest_abs t2 in
        let n1 = fst(dest_var v1) and n2 = fst(dest_var v2) in
        let newacc = if n1 = n2 then acc else insert (n1,n2) acc in
        match_bvs b1 b2 newacc
    with Failure _ -> try
        let l1,r1 = dest_comb t1
        and l2,r2 = dest_comb t2 in
        match_bvs l1 l2 (match_bvs r1 r2 acc)
    with Failure _ -> acc in
  fun avoids metas th ->
    let sth = SPEC_ALL th in
    let bod = concl th in
    let lconsts = subtract (union avoids (intersect (frees (concl th)) (freesl(hyp th)))) metas in
    fun tm ->
      let bvms = match_bvs tm bod [] in
      let abod = deep_alpha bvms bod in
      seq_match lconsts metas bod tm;;
(*      let insts = seq_match lconsts metas abod tm in
      let fth = INSTANTIATE insts ath in
      (*      if hyp fth <> hyp ath then failwith "PART_MATCH: instantiated hyps" else*)
      let tm' = concl fth in
      if Pervasives.compare tm' tm = 0 then (fth,insts) else
      try SUBS[ALPHA tm' tm] fth,insts
      with Failure _ -> failwith "PART_MATCH: Sanity check failure";;
 *)
 *)

(* ------------------------------------------------------------------------- *)
(* Matching a sequent-based theorem (assumption) to a term.                  *)
(* See Isabelle Light on why we need these.                                  *)
(* We just use our sequent matcher instead of term_match.                    *)
(* ------------------------------------------------------------------------- *)

let REV_PART_SEQMATCH_I =
  let rec match_bvs t1 t2 acc =
    try let v1,b1 = dest_abs t1
        and v2,b2 = dest_abs t2 in
        let n1 = fst(dest_var v1) and n2 = fst(dest_var v2) in
        let newacc = if n1 = n2 then acc else insert (n1,n2) acc in
        match_bvs b1 b2 newacc
    with Failure _ -> try
        let l1,r1 = dest_comb t1
        and l2,r2 = dest_comb t2 in
        match_bvs l1 l2 (match_bvs r1 r2 acc)
    with Failure _ -> acc in
  fun avoids metas th ->
    let bod = concl th in
    let lconsts = subtract (union avoids (intersect (frees (concl th)) (freesl(hyp th)))) metas in
    fun tm ->
      let bvms = match_bvs bod tm [] in
      let atm = deep_alpha bvms tm in
      seq_match lconsts metas atm bod;; 


let rec (term_to_asm_seqmatch: term list -> term list ->
	 term -> (string * thm) list -> (string * thm) list * ((string * thm) * instantiation)) =
  fun avoids metas key asms ->
    if (asms = []) then failwith ("No assumptions match `" ^ (string_of_term key) ^ "`!")
    else try 
      let l,asm = hd asms in
      let i = REV_PART_SEQMATCH_I avoids metas asm key in
      (tl asms),((l,asm),i)
    with Failure _ -> 
      let res,inst = term_to_asm_seqmatch avoids metas key (tl asms) in 
	((hd asms)::res),inst;;


let rec (term_to_asm_lbl_seqmatch: term list -> term list ->
	 term -> (string * thm) list -> 
	 string -> (string * thm) list * ((string * thm) * instantiation)) =
  fun avoids metas key asms lbl ->
    let (l,asm),re_asms = try ( remove (fun l,_ -> l = lbl) asms ) 
      with Failure _ -> failwith "No such assumption found!" in
    let i = try ( REV_PART_SEQMATCH_I avoids metas asm key )
      with Failure _ -> 
	failwith ("Assumption `" ^ 
		     ((string_of_term o concl) asm) ^ 
		     "` doesn't match `" ^ (string_of_term key) ^ "`!") in
    re_asms,((l,asm),i);;



type seqtactic = (int * term list) etactic;;

(* ------------------------------------------------------------------------- *)
(* apply_seqtac does more than its Isabelle Light counter part.              *)
(* - It renames variables in the theorem (rule) into fresh variables. Also   *)
(* renames the instlist so that the variables there match.                   *)
(* - It eliminates empty multisets (mempty) in  both the conclusion and      *)
(* the assumptions.                                                          *)
(* - Upon failure restores the counter in an attempt for some bookkeeping.   *)
(* ------------------------------------------------------------------------- *)

let (apply_seqtac:(?glfrees:term list)->((term list)->(term * term) list -> meta_rule -> (term list) etactic) ->
  (term * term) list -> meta_rule -> seqtactic) =
  fun ?(glfrees=[]) rtac instlist rl (ctr,metas) gl ->
    let glf = if (glfrees = []) then gl_frees gl else glfrees in
    let fnum = if (ctr < 0) then fresh_proofctr () else ctr + 1 in
    let finstlist = number_vars_instlist fnum instlist
    and frl = number_vars_meta_rule fnum rl in
    let gstate,newmetas = ETHEN (rtac glf finstlist frl)
				(ETAC ( TRY CONJ_TAC THEN CONV_TAC NORM_MSET_CONV )) metas gl in
    gstate, ((if (ctr < 0) then ctr else ctr + 1),newmetas);;

let create_seq_goal:(string * thm) list -> goal -> goal =
  fun asms (hs,gl) ->
    let hs' = map (fun (s,asm) -> s,NORMALIZE_MULTISET_ALL asm) hs in
    (hs'@asms,(rhs o concl o NORM_MSET_CONV) gl);;
 
(* ------------------------------------------------------------------------- *)
(* RULE / RULE_TAC for embedded sequent calculus logics.                     *)
(* ------------------------------------------------------------------------- *)

let (rulem_seqtac:(term list)->(term*term) list->meta_rule->(term list) etactic) =
  fun glf instlist r metas ((asl,w) as g) ->
    let r = inst_meta_rule_vars instlist r glf in  
    let rmetas = subtract (meta_rule_frees r) (itlist union (map (frees o snd) instlist) glf)  in
    let avoids = subtract glf metas in
    
    let ins = try ( seq_match avoids (rmetas@metas) (fst3 r) w ) 
	     with Failure s -> failwith ("Rule doesn't match: " ^ s) in

    let (c,new_hyps,thm) as ri = inst_meta_rule ins r
    and (asl,w) as g = inst_goal ins g in

    let new_goals = map (create_seq_goal asl) new_hyps in

    (* Instantiate types (thd3 ins) to deal with polymorphic goals. *)
    let newmetas = intersect (map (inst (thd3 ins)) rmetas) (meta_rule_frees ri) in

    let rec create_dischl = 
      fun (asms,g) -> if (asms = []) then [] else 
	((concl o snd o hd) asms)::(create_dischl ((tl asms),g)) in
    let dischls = map create_dischl new_hyps in

    ((newmetas,ins),new_goals,fun i l ->  
      let thm = INSTANTIATE_ALL i thm in (* NORM_MSET_INST_ALL i thm in *)
      let thm2 = PROVE_MULTISET_EQ (concl thm) (instantiate i w) in

      let res = List.fold_left 
	(fun t1 t2 -> MSET_PROVE_HYP (INSTANTIATE_ALL i t2) t1) thm 
	(map (dischi_pair i) (zip dischls l)) in
(*
      print_string "r:" ; print_thm res ; print_newline(); 
  print_string "ret:" ; print_thm (EQ_MP (INSTANTIATE_ALL i thm2) res) ; print_newline();
*)
      EQ_MP thm2 res),newmetas@metas;;


let rule_seqtac ?(glfrees=([]:term list)) instlist thm = apply_seqtac ~glfrees:glfrees rulem_seqtac instlist (mk_meta_rule thm);;

let ruleseq ?(glfrees=([]:term list)) = rule_seqtac ~glfrees:glfrees [];;

(* ------------------------------------------------------------------------- *)
(* ERULE / ERULE_TAC  for embedded sequent calculus logics.                  *)
(* ------------------------------------------------------------------------- *)      

let (erulem_seqtac:?lbl:string->(term list)->(term*term) list->meta_rule->(term list) etactic) =
  fun ?(lbl="") glf instlist rl metas ((asl,w) as gl) -> 
    let r = inst_meta_rule_vars instlist rl glf in
    let rmetas = subtract (meta_rule_frees r) (itlist union (map (frees o snd) instlist) glf)  in
    let avoids = subtract glf metas in

    let ins = try ( seq_match avoids (rmetas@metas) (fst3 r) w ) 
    with Failure s -> failwith ("Rule doesn't match: " ^ s) in

    let (cn,hyps,thm) as rl = inst_meta_rule ins r in    
    let (asl,w) as gl = inst_goal ins gl in
    let rmetas' = intersect (map (inst (thd3 ins)) rmetas) (meta_rule_frees rl) in
    
    let (prems,major_prem) = 
      if (hyps = []) then failwith "erule: Not a proper elimination rule: no premises!" 
      else hd hyps in
    
    let asl,((lbl,major_thm),elim_inst) = 
      if (prems = [])
      then 
        try if (String.length lbl = 0)
	    then term_to_asm_seqmatch avoids (rmetas'@metas) major_prem asl
	    else term_to_asm_lbl_seqmatch avoids (rmetas'@metas) major_prem asl lbl
	with Failure s -> failwith ("erule: " ^ s) 
      else failwith "erule: not a proper elimination rule: major premise has assumptions!" in

    let (_,major_asm)::new_hyps = map (inst_goal elim_inst) hyps in
    let new_goals = map (inst_goal elim_inst o create_seq_goal asl) new_hyps in
    let thm = INSTANTIATE_ALL elim_inst thm in

    let rec create_dischl = 
      fun (asms,g) -> 
	if (asms = []) then [] 
	else ((concl o snd o hd) asms)::(create_dischl ((tl asms),g)) in
    let dischls = map create_dischl new_hyps in
      
    let newmetas = intersect (map (inst (thd3 elim_inst)) rmetas') (thm_frees thm) in

    ((newmetas,compose_insts ins elim_inst),new_goals,fun i l ->
      let einst = compose_insts elim_inst i in
      let thm = INSTANTIATE_ALL i thm in
      let thm2 = PROVE_MULTISET_EQ (concl thm) (instantiate einst w) in
      let major_thmi = INSTANTIATE_ALL einst major_thm in

      let l = (major_thmi :: map (ADD_HYP major_thmi) (map (dischi_pair i) (zip dischls l))) in 
      let res = List.fold_left (fun t1 t2 -> MSET_PROVE_HYP (INSTANTIATE_ALL i t2) t1) thm l in
      EQ_MP thm2 res),newmetas@metas;;

let erule_seqtac ?(lbl="") ?(glfrees=([]:term list)) instlist thm =
  apply_seqtac ~glfrees:glfrees (erulem_seqtac ~lbl:lbl) instlist (mk_meta_rule thm);;

let eruleseq ?(lbl="") ?(glfrees=([]:term list)) = erule_seqtac ~lbl:lbl ~glfrees:glfrees [];;


(* ------------------------------------------------------------------------- *)
(* DRULE / DRULE_TAC  for embedded sequent calculus logics.                  *)
(* ------------------------------------------------------------------------- *)      

let (drulem_seqtac:?lbl:string->string->(term list)->(term*term) list->meta_rule->(term list) etactic) =
  fun ?(lbl="") reslbl glf instlist rl metas ((asl,w) as gl) -> 
    let ((cn,hyps,thm) as rl) = inst_meta_rule_vars instlist rl glf in
    let rmetas = subtract (meta_rule_frees rl) (itlist union (map (frees o snd) instlist) glf)  in
    let avoids = subtract glf metas in

    let (prems,major_prem) = 
      if (hyps = []) then failwith "drule: Not a proper destruction rule: no premises!" 
      else hd hyps in
   
    let asl,((lbl,major_thm),elim_inst) = 
      if (prems = [])
      then 
        try if (String.length lbl = 0)
	    then term_to_asm_seqmatch avoids (rmetas@metas) major_prem asl
	    else term_to_asm_lbl_seqmatch avoids (rmetas@metas) major_prem asl lbl
	with Failure s -> failwith ("drule: " ^ s) 
      else failwith "drule: not a proper destruction rule: major premise has assumptions!" in

    let (_,major_asm)::new_hyps = map (inst_goal elim_inst) hyps in
   let thm = INSTANTIATE_ALL elim_inst thm in
 
    let new_goals = (map (create_seq_goal asl) new_hyps) @ 
      [create_seq_goal asl ([reslbl,ASSUME (instantiate elim_inst cn)],w)] in
    
    let rec create_dischl = 
      fun (asms,g) -> 
	if (asms = []) then [] 
	else ((concl o snd o hd) asms)::(create_dischl ((tl asms),g)) in
    (* We add an empty discharge list at the end for the extra goal. *)
    let dischls = map create_dischl new_hyps @ [[]] in

    let newmetas = intersect (map (inst (thd3 elim_inst)) rmetas) (thm_frees thm) in

    ((newmetas,elim_inst),new_goals,fun i l ->
      let einst = compose_insts elim_inst i in
      let thm = INSTANTIATE_ALL i thm in
      let major_thmi = INSTANTIATE_ALL einst major_thm in

      let l = (major_thmi :: map (ADD_HYP major_thmi) (map (dischi_pair i) (zip dischls l))) in
      MSET_PROVE_HYP (List.fold_left (fun t1 t2 -> MSET_PROVE_HYP (INSTANTIATE_ALL i t2) t1) thm (butlast l)) 
	(last l)),newmetas@metas;;

let drule_seqtac ?(lbl="") ?(reslbl="") ?(glfrees=([]:term list)) instlist thm =
  apply_seqtac ~glfrees:glfrees (drulem_seqtac ~lbl:lbl reslbl) instlist (mk_meta_rule thm);;

let druleseq ?(lbl="") ?(reslbl="") ?(glfrees=([]:term list)) = drule_seqtac ~lbl:lbl ~reslbl:reslbl ~glfrees:glfrees [];;


(* ------------------------------------------------------------------------- *)
(* FRULE / FRULE_TAC  for embedded sequent calculus logics.                  *)
(* ------------------------------------------------------------------------- *)      

let (frulem_seqtac:?lbl:string->string->(term list)->(term*term) list->meta_rule->(term list) etactic) =
  fun ?(lbl="") reslbl glf instlist rl metas ((asl,w) as gl) -> 
    let ((cn,hyps,thm) as rl) = inst_meta_rule_vars instlist rl glf in
    let rmetas = subtract (meta_rule_frees rl) (itlist union (map (frees o snd) instlist) glf)  in
    let avoids = subtract glf metas in

    let (prems,major_prem) = 
      if (hyps = []) then 
	failwith "frule: Not a proper destruction rule: no premises!" 
      else hd hyps in
 
    let _,((lbl,major_thm),elim_inst) = 
      if (prems = [])
      then 
        try if (String.length lbl = 0)
	    then term_to_asm_seqmatch avoids (rmetas@metas) major_prem asl
	    else term_to_asm_lbl_seqmatch avoids (rmetas@metas) major_prem asl lbl
	with Failure s -> failwith ("frule: " ^ s) 
      else 
	failwith "frule: not a proper destruction rule: major premise has assumptions!" in

    let (_,major_asm)::new_hyps = map (inst_goal elim_inst) hyps in
    let thm = INSTANTIATE_ALL elim_inst thm in

    let create_goal = fun asms (hs,gl) -> inst_goal elim_inst (hs@asms,gl) in
    let new_goals = (map (create_goal asl) new_hyps) @ 
      [create_goal asl ([reslbl,ASSUME (instantiate elim_inst cn)],w)] in

    let rec create_dischl = 
      fun (asms,g) -> 
	if (asms = []) then [] 
	else ((concl o snd o hd) asms)::(create_dischl ((tl asms),g)) in
    (* We add an empty discharge list at the end for the extra goal. *)
    let dischls = map create_dischl new_hyps @ [[]] in

    let newmetas = intersect (map (inst (thd3 elim_inst)) rmetas) (thm_frees thm) in

    ((newmetas,elim_inst),new_goals,fun i l ->
      let einst = compose_insts elim_inst i in
      let thm = INSTANTIATE_ALL i thm in
      let major_thmi = INSTANTIATE_ALL einst major_thm in

      let l = (major_thmi ::map (dischi_pair i) (zip dischls l)) in
      MSET_PROVE_HYP (List.fold_left (fun t1 t2 -> MSET_PROVE_HYP (INSTANTIATE_ALL i t2) t1) thm (butlast l)) 
	(last l)),newmetas@metas;;

	
let frule_seqtac ?(lbl="") ?(reslbl="") ?(glfrees=([]:term list)) instlist thm =
  apply_seqtac ~glfrees:glfrees (frulem_seqtac ~lbl:lbl reslbl) instlist (mk_meta_rule thm);;

let fruleseq ?(lbl="") ?(reslbl="") ?(glfrees=([]:term list)) = frule_seqtac ~lbl:lbl ~reslbl:reslbl ~glfrees:glfrees [];;

					


(* ------------------------------------------------------------------------- *)
(* "e" tactic application for the embedded logic tactics.                    *)
(* ------------------------------------------------------------------------- *)
						   
let eseq:seqtactic -> goalstack =
  fun tac -> e (ETAC_TAC (-1,(try(top_metas(p())) with Failure _ -> ([]:term list))) tac);;

(* ------------------------------------------------------------------------- *)
(* Convert a tactic to a seqtactic.                                          *)
(* ------------------------------------------------------------------------- *)
(*
let SEQTAC = ETAC_TAC (-1,(try(top_metas(p())) with Failure _ -> ([]:term list)));;
 *)
let SEQTAC:tactic->seqtactic =
  fun tac (i,m) gl ->
    let ((metas,_),_,_) as gs = tac gl in
    gs,(i,metas@m);;

(* ------------------------------------------------------------------------- *)
(* "prove" a theorem using the embedded logic tactics.                       *)
(* ------------------------------------------------------------------------- *)

let prove_seq:term * seqtactic -> thm =
  fun (tm,tac) -> prove(tm,ETAC_TAC (0,([]:term list)) tac);;

  
(* ------------------------------------------------------------------------- *)
(* Assumption matching using seq_match.                                      *)
(* ------------------------------------------------------------------------- *)
(* Essentially tries to apply an assumption as a meta rule.                  *)
(* This takes advantage of multiset matching and metavariables.              *)
(* ------------------------------------------------------------------------- *)

(*
let seqassumption :seqtactic =
  fun (i,metas) ->
  ETAC (PURE_REWRITE_ASM_TAC[MUNION_AC] THEN 
   REWRITE_TAC[MUNION_AC] THEN (assumption ORELSE meta_assumption metas)) (i,metas);;
 *)

let (MATCH_ACCEPT_SEQTAC:thm -> seqtactic) =
  fun th (i,metas) (asl,w) ->
  let avoids = subtract (frees w) metas in
  try let inst = REV_PART_SEQMATCH_I avoids metas th w in
	  let thm = INSTANTIATE_ALL inst th in
	  
	  (([],inst),[],fun i [] ->
	                let finst = compose_insts inst i in
	                let thm = INSTANTIATE_ALL i thm in
	                let thm2 = PROVE_MULTISET_EQ (concl thm) (instantiate finst w) in
	                EQ_MP thm2 thm),(i,metas)
  with Failure s -> failwith ("MATCH_ACCEPT_SEQTAC: " ^ s);;

let seqassumption :seqtactic =
  fun (i,metas) (asl,w as g) ->
    tryfind (fun (_,th) -> MATCH_ACCEPT_SEQTAC th (i,metas) g) asl;;

(* ------------------------------------------------------------------------- *)
(* Matching labelled assumptions.                                            *)
(* ------------------------------------------------------------------------- *)
  
(*
let prove_by_seq : string -> seqtactic =
  fun lbl (i,metas) -> ETAC (
    PURE_REWRITE_TAC[MUNION_AC] THEN 
    ((USE_THEN lbl (MATCH_ACCEPT_TAC o PURE_REWRITE_RULE[MUNION_AC]) ORELSE 
    (USE_THEN lbl (ALL_UNIFY_ACCEPT_TAC metas o PURE_REWRITE_RULE[MUNION_AC]))))) (i,metas);;
 *)

let prove_by_seq : string -> seqtactic =
  fun s (i,metas) (asl,w as gl) ->
      let th = try assoc s asl with Failure _ ->
	failwith("USE_TAC: didn't find assumption "^s) in
      MATCH_ACCEPT_SEQTAC th (i,metas) gl;;

(* ------------------------------------------------------------------------- *)
(* Tactic to cut with a known lemma in the embedded logic.                   *)
(* ------------------------------------------------------------------------- *)
(* TODO
let cut_seqtac =
  fun setlist thm ->
    let thm = (UNDISCH_ALL o MIMP_TO_IMP_RULE o SPEC_ALL) thm in
    let primed_ll_cut = inst_meta_rule_vars [] (mk_meta_rule ll_cut) (thm_frees thm) in
    let cut_term = (hd o tl o hyp o thd3) primed_ll_cut in
    let cut_ins = ll_term_match (thm_frees thm) cut_term (concl thm) in
    let new_rule = inst_meta_rule (cut_ins) primed_ll_cut in
    llapply llrulem_tac setlist new_rule 

(*
let llcut_tac = 
  fun setlist thm ->
    let thm = (UNDISCH_ALL o MIMP_TO_IMP_RULE o SPEC_ALL) thm in
    let primed_ll_cut = thm_mk_primed_vars (thm_frees thm) ll_cut in
    let cut_term = (snd o dest_conj o fst o dest_mimp o concl) primed_ll_cut in
    let cut_ins = ll_rule_match (thm_frees thm) cut_term (concl thm) in
    let ll_cut_inst = INSTANTIATE cut_ins primed_ll_cut in
    let ADD_DISCH d t = DISCH d (ADD_HYP (ASSUME d) t) in
    let new_rule = MIMP_RULE (List.fold_right ADD_DISCH (fst (dest_thm thm)) ll_cut_inst) in
    llapply (llrulem_tac setlist (mk_meta_rule new_rule)) ;;
*)

let llcut = llcut_tac []
 *)

let (META_EXISTS_SEQTAC:seqtactic) =
  fun (i,metas) ((asl,w) as gl) ->
  let v = fst(dest_exists w) in
  let avoids = itlist (union o frees o concl o snd) asl (frees w) in
  let v' = mk_primed_var avoids v in
  X_META_EXISTS_TAC v' gl,(i,v' :: metas);;

  

let seqstatestr (i,metas) =
  "Ctr: " ^ (string_of_int i) ^ " | Metas: " ^ (String.concat ", " (map string_of_term metas));;

let print_seqstate st = print_string (seqstatestr st); print_newline();;

(* ------------------------------------------------------------------------- *)

