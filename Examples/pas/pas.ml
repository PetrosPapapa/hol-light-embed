(* ========================================================================= *)
(* The Propositions-as-Sessions paradigm.                                    *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                 2012-2019                                 *)
(* ========================================================================= *)

(* Dependencies *)

needs "tools/lib.ml";;
needs "embed/sequent.ml";;
needs "embed/LL/pas/cp.ml";;
needs "embed/LL/pas/CLL.ml";;

(* Type definition: Linear Proposition with a proof term attached to it. *)

let linterm_INDUCT,linterm_RECURSION = define_type "LinTerm = LL A LinProp";;

parse_as_infix("<>",(16,"right"));;
override_interface("<>",`LL`);;

new_type_abbrev("CProc",`:(num,LinProp)CProcess`);;

(* ------------------------------------------------------------------------- *)
(* Linear consequence                                                        *)
(* ------------------------------------------------------------------------- *)
(* We use a one-sided sequent calculus, process calculus proof terms and     *)
(* include the process calculus translations for each rule.                  *)
(* Instead of having an Exchange rule, we use multisets. Our embedded prover *)
(* then does the matching automatically (see CLL_prover.ml) thus keeping our *)
(* proofs nice and clean.                                                    *)
(* ------------------------------------------------------------------------- *)
(* The rules for the exponentials are not included (yet).                    *)
(* ------------------------------------------------------------------------- *)

let linear_RULES,linear_INDUCT,linear_CASES = new_inductive_definition
  `(!(A:LinProp) (x:num) y. 
       |-- (' (y <> NEG A) ^ ' (x <> A)) 
      (y <-> x)) /\
  (!x.
      |-- (' (x <> LinOne)) (EOut x)) /\
  (!x G P. 
      |-- G P ==>
      |-- (G ^ ' (x <> Bottom)) (EIn x P)) /\
  (!x G. 
      |-- (G ^ ' (x <> Top)) (ECase x)) /\
  (!x y P Q A B G D. 
     (|-- (G ^ ' (x <> A)) P) /\ 
     (|-- (D ^ ' (y <> B)) Q) ==> 
     (|-- (G ^ D ^ ' (y <> (A ** B))) 
	 (Out y x P Q))) /\
  (!x y P A B G. 
     (|-- (G ^ ' (x <> A) ^ ' (y <> B)) P) ==> 
     (|-- (G ^ ' (y <> (A % B))) 
	 (In y x P))) /\
  (!x P A B G. 
     (|-- (G ^ ' (x <> A)) P) ==> 
     (|-- (G ^ ' (x <> (A ++ B))) 
	 (Inl x P))) /\
  (!y P A B G. 
     (|-- (G ^ ' (y <> B)) P) ==> 
     (|-- (G ^ ' (y <> (A ++ B))) 
	 (Inr y P))) /\
  (!x P Q A B G. 
     (|-- (G ^ ' (x <> A)) P) /\ 
     (|-- (G ^ ' (x <> B)) Q) ==> 
     (|-- (G ^ ' (x <> (A && B))) 
	 (Case x P Q))) /\
  (!x y Q A D. 
     (|-- (D ^ ' (x <> ?? A) ^ ' (y <> ?? A)) Q) ==> 
     (|-- (D ^ ' (x <> ?? A)) (cpSUB1 NCH Q (y,x)))) /\
  (!x y Q A D. 
     (|-- (D ^ ' (y <> A)) Q) ==> 
     (|-- (D ^ ' (x <> ?? A))
          (ROut x y Q))) /\
  (!x Q A D. 
     (|-- D Q) ==> 
     (|-- (D ^ ' (x <> ?? A)) Q)) /\
  (!x P Q G C D. 
     (|-- (' (x <> NEG C) ^ D) Q) /\
     (|-- (G ^ ' (x <> C)) P) ==> 
     (|-- (G ^ D) 
	 (Par x C P Q)))
  `;;

(* TODO
Missing ! rule because we don't have IMAGE for multisets (but we can't handle the side condition anyway).
*)

(* Linear Logic meta-rules (Isabelle Light). *)

let [ll_id;
     ll_one;
     ll_bottom;
     ll_top;
     ll_times;
     ll_par;
     ll_plus1; ll_plus2;
     ll_with;
     ll_contract;
     ll_whynot;
     ll_weaken;
     ll_cut  ] = 
  map (MIMP_RULE o SPEC_ALL o REWRITE_RULE[IMP_CONJ]) 
    (CONJUNCTS linear_RULES);;




(* ------------------------------------------------------------------------- *)
(* Getter functions for various parts of a CLL sequent.                      *)
(* ------------------------------------------------------------------------- *)

(* Get all types (LinProp) in a CLL sequent. *)
let get_ll_props = 
 map (rand o rand) o (filter is_msing) o flat_munion o rand o rator;;

(* Get all types that satisfy f. *)
let find_ll_props f = 
  (filter f) o get_ll_props;;

(* Get the first type that satisfies f. *)
let find_ll_prop f = 
  (find f) o get_ll_props;;

(* Get all terms (LinTerm) in a CLL sequent. *)
let get_ll_terms = 
 map (rand) o (filter is_msing) o flat_munion o rand o rator;;

(* Get all terms whose types satisfy f. *)
let find_ll_terms f = 
  (filter (f o rand)) o get_ll_terms;;

(* Get the first term whose type satisfies f. *)
let find_ll_term f = 
  (find (f o rand)) o get_ll_terms;;

(* Get the list of free channels input terms. *)
let get_ll_channels = 
 map (rand o rator o rand) o (filter is_msing) o flat_munion o rand o rator;;

let gen_ll_channels tm =
  list_mk_forall (get_ll_channels tm,tm);;


(* Find the first output (positive term) of a sequent. *)
let find_output =
  find_ll_prop 
    ( fun x -> try (let _ = find_term ((=) `(NEG)`) x in false ) with Failure _ -> true);;

(* Get the list of negated (input) terms. *)
let find_input_terms =
  (find_ll_terms is_llneg);;



(* ------------------------------------------------------------------------- *)
(* Derived rules                                                             *)
(* ------------------------------------------------------------------------- *)
				     
let ll_id' = prove_seq (`|-- (' (y <> NEG A)^' (x <> A)^'(z <> ?? C)) (y <-> x)`,
			     ETHEN (ruleseq ll_weaken) (ruleseq ll_id));;

let ll_one' = prove_seq (`|-- (' (x <> LinOne)^'(z <> ?? C)) (EOut x)`,
			      ETHEN (ruleseq ll_weaken) (ruleseq ll_one));;

let ll_cd = prove_seq (`|-- (G ^'(x <> ??A)^'(y <> A)) Q ===> |-- (G ^'(x <> ??A)) (cpSUB1 NCH (ROut w y Q) (w,x))`,
			   EEVERY[ ETAC (MIMP_TAC THEN DISCH_TAC);
				   ruleseq ll_contract;
				   rule_seqtac [`x`,`w`] ll_whynot;
				   seqassumption]);;


(* ------------------------------------------------------------------------- *)
(* Automated tactics                                                         *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* BUFFER_TAC tries to automatically prove any arbitrarily complex buffer.   *)
(* ie. it proves `|-- (' (_ <> NEG A) ^ ' (_ <> A)) _` where `A` is an       *)
(* arbitrarily complex output term (ie. only contains positive literals,     *)
(* times ( ** ) and plus ( ++ )).                                            *)
(* ------------------------------------------------------------------------- *)
(* Note that the times case is treated with a special tactic because of      *)
(* context splitting.                                                        *)
(* ------------------------------------------------------------------------- *)

let rec (BUFFER_ETAC:seqtactic) =
  let timestac lh rh s ((_,tm) as gl) =
    let nlh,nrh = hashf mk_llneg (lh,rh) in
    let nltm = mk_msing ( find_ll_term ((=) nlh) tm )
    and nrtm = mk_msing ( find_ll_term ((=) nrh) tm ) in
    rule_seqtac [(`A:LinProp`,lh);
		 (`B:LinProp`,rh);
		 (`G:(LinTerm)multiset`,nltm);
		 (`D:(LinTerm)multiset`,nrtm)] ll_times s gl
  in
  fun s ((_,tm) as gl) ->
  try (
    let out = find_output tm in
    if (is_var out) then ( ruleseq ll_id s gl )
    else
    let comb,args = strip_comb out in
    if (comb = `LinTimes`)
    then let lh,rh = hd args,(hd o tl) args in
	 let tac = EEVERY
		   [ETAC (ONCE_REWRITE_TAC[NEG_CLAUSES]);
		    ruleseq ll_par;
		    timestac lh rh;
		    BUFFER_ETAC ] in
	 tac s gl
    else if (comb = `LinPlus`)
    then let tac =
	   ETHEN (
	   ETHENL (
	   EEVERY [ETAC (ONCE_REWRITE_TAC[NEG_CLAUSES]);
		   ruleseq ll_with])
		  [ ruleseq ll_plus1 ;
		    ruleseq ll_plus2 ])
		 BUFFER_ETAC in
	 tac s gl
    else
    failwith ("Unable to handle combinator: " ^ (string_of_term comb))
  ) with Failure st -> failwith ("BUFFER_TAC: " ^ st);;
			       


(* ------------------------------------------------------------------------- *)
(* cllCombSelect prioritizes CLL term by size. In proof search, we prefer    *)
(* trying shorter terms first as they may fail faster.                       *)
(* ------------------------------------------------------------------------- *)

let cllCombSelect tm =
  if (not (is_comb tm))
  then 0
  else let comb,args = strip_comb tm in
       let l,r = hd args,(hd o tl) args in
       if ((is_var l) || (is_const l)) then -1
       else if ((is_var r) || (is_const r)) then 1 
       else (term_size l) - (term_size r);;
			    

(* ------------------------------------------------------------------------- *)
(* MALL_PROVE_INPUT_ETAC breaks down the input term NEG A using the par and  *)
(* with rules. There is no branching in this process so we just run          *)
(* it until NEG A has been broken down to atomic (negative) literals.        *)
(* ------------------------------------------------------------------------- *)
(* TODO: The cllCombSelect selection here doesn't make sense as we run the   *)
(* tactic exchaustively anyway. What would make sense is to reorder the      *)
(* subgoals so that the smaller subgoal is tested first at the next stage.   *)
(* ------------------------------------------------------------------------- *)

let rec (MALL_PROVE_INPUT_ETAC:seqtactic) =
  fun s gl ->
  let rec withProof s ((_,tm) as gl) =
    let wtm = find_ll_prop (is_binary "LinWith") tm in
    let comb,args = strip_comb wtm in
    let lh,rh = hd args,(hd o tl) args in
    let select = cllCombSelect wtm in
    if (select <= 0)
    then (ETHEN
	  (rule_seqtac [(`A:LinProp`,lh);
			(`B:LinProp`,rh)] ll_with)
	  MALL_PROVE_INPUT_ETAC) s gl
    else (ETHEN
	  (ETHENL
	   (rule_seqtac [(`A:LinProp`,lh);
			 (`B:LinProp`,rh)] ll_with)
	   [ALL_ETAC;MALL_PROVE_INPUT_ETAC])
	  MALL_PROVE_INPUT_ETAC) s gl in
  EEVERY [
  ETAC (simp[NEG_CLAUSES]) ;
  EREPEAT (ruleseq ll_par) ;
  EREPEAT withProof ] s gl;;
	 
	
(* ------------------------------------------------------------------------- *)
(* MALL_PROVE_OUTPUT1_ETAC assumes all inputs are atomic and tries to prove  *)
(* the output using the times and plus rules.                                *)
(* Both these rules involve branching/searching so we prioritize by term     *)
(* size. Atomic terms are the fastest to test as they only allow a unique use*)
(* of the times rule that only carries their negative counterpart in the     *)
(* context split.                                                            *)
(* Focusing is automatic here as we assume only 1 positive term.             *)
(* ------------------------------------------------------------------------- *)

let rec (MALL_PROVE_1OUTPUT_ETAC:seqtactic) =
  fun s ((_,tm) as gl) ->
  try (
  let out = find_output tm in
  if (is_var out) then ( ruleseq ll_id s gl )
  else let comb,args = strip_comb out in
       if (comb = `LinTimes`)
       then let lh,rh = hd args,(hd o tl) args in
	    if (is_var lh)
	    then let nlh = mk_llneg lh in
		 let nltm = mk_msing ( find_ll_term ((=) nlh) tm ) in
		 (ETHEN
		  (rule_seqtac [(`A:LinProp`,lh);
				(`B:LinProp`,rh);
				(`G:(LinTerm)multiset`,nltm)] ll_times)
		  MALL_PROVE_1OUTPUT_ETAC) s gl
	    else if (is_var rh)
	    then let nrh = mk_llneg rh in
		 let nrtm = mk_msing ( find_ll_term ((=) nrh) tm ) in
		 (ETHEN
		  (ETHENL
		   (rule_seqtac [(`A:LinProp`,lh);
				    (`B:LinProp`,rh);
				    (`D:(LinTerm)multiset`,nrtm)] ll_times)
		   [ ALL_ETAC ; MALL_PROVE_1OUTPUT_ETAC ])
		  MALL_PROVE_1OUTPUT_ETAC) s gl
	    else
	    let iterms = find_input_terms tm in
	    let rec PROVE_TENSOR index =
	      match nextSubsetIndex(index) with
		| None -> failwith "MALL_PROVE_1OUTPUT_ETAC"
		| Some(i) ->
		    let subset = getIndexedSubset i iterms in
		    let dcontext = list_mk_munion (map mk_msing subset) in
		    let tac = rule_seqtac [(`A:LinProp`,lh);
					   (`B:LinProp`,rh);
					   (`D:(LinTerm)multiset`,dcontext)] ll_times in
		    let select = cllCombSelect out in
		    if (select <= 0)
		    then 
		    (EORELSE (ETHEN tac MALL_PROVE_1OUTPUT_ETAC) (PROVE_TENSOR i))
		    else
		    (EORELSE (ETHEN 
			      (ETHENL tac [ ALL_ETAC ; MALL_PROVE_1OUTPUT_ETAC ])
			      MALL_PROVE_1OUTPUT_ETAC)
			     (PROVE_TENSOR i)) in
	    PROVE_TENSOR (createSubsetIndex iterms) s gl
		       
       else if (comb = `LinPlus`)
       then let select = cllCombSelect out in
	    if (select <= 0)
	    then (EORELSE (ETHEN (ruleseq ll_plus1) MALL_PROVE_1OUTPUT_ETAC)
			  (ETHEN (ruleseq ll_plus2) MALL_PROVE_1OUTPUT_ETAC)) s gl
	    else (EORELSE (ETHEN (ruleseq ll_plus2) MALL_PROVE_1OUTPUT_ETAC)
			  (ETHEN (ruleseq ll_plus1) MALL_PROVE_1OUTPUT_ETAC)) s gl
										   
       else
       failwith "MALL_PROVE_1OUTPUT_ETAC"    
  ) with Failure _ -> failwith "MALL_PROVE_1OUTPUT_ETAC";;
			       
			       

(* ------------------------------------------------------------------------- *)
(* CLL_TAC is an automated CLL prover for sequents of the form:              *)
(* |-- (NEG A), B                                                            *)
(* where A and B only contain positive literals, plus, and times.            *)
(* We call such lemmas "filters" and they correspond to properties of CLL.   *)
(* ------------------------------------------------------------------------- *)
	
let (CLL_TAC:seqtactic) =
  fun s gl ->
  try (
  EEVERY [
  MALL_PROVE_INPUT_ETAC;
  MALL_PROVE_1OUTPUT_ETAC] s gl
  ) with Failure s -> failwith ("CLL_TAC: " ^ s);;
