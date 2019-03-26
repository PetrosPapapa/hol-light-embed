(* ========================================================================= *)
(* Deep embedding of Intuitionistic Linear Logic                             *)
(*                                                                           *)
(* Petros Papapanagiotou                                                     *)
(* Center of Intelligent Systems and their Applications                      *)
(* University of Edinburgh                                                   *)
(* 2019                                                                      *)
(* ------------------------------------------------------------------------- *)
(* This includes the rules of a subset of the simply-typed lambda calculus 
   of Church, as presented in Section 7 of the following paper:

   Wadler, P 2015, 'Propositions as Types' 
   Communications of the ACM, vol 58, no. 12, pp. 75-84. 
   DOI: 10.1145/2699407
   https://dl.acm.org/citation.cfm?doid=2847579.2699407
   http://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf

   The subset only includes conjunction/products and implication/funtions for
   demonstration purposes.

   We convert the rules from natural deduction to sequent calculus following:
   Girard, J.Y., Taylor, P. and Lafont, Y., 1989. 'Proofs and types'
   Cambridge: Cambridge university press.

   We embed the logic alone (|=) as well as its correspondence (|==).
                                                                             *)
(* ========================================================================= *)

(* Dependencies *)
loads ("embed/sequent.ml");;

(* Type declaration *)

let prop_INDUCT,prop_RECURSION = define_type
    "Prop = Truth
     | Product Prop Prop
     | Implies Prop Prop";;

(* Pretty printing abbreviations *)

parse_as_infix("-->",(13,"right"));;
override_interface("-->",`Implies`);;
parse_as_infix("%",(14,"right"));;
override_interface("%",`Product`);;

(* Consequence operator *)
parse_as_infix("|=",(11,"right"));;

(* Consequence rules *)
let propRULES,propINDUCT,propCASES = new_inductive_definition 
`(!a. ' a |= a) /\

 (!G a c. (G |= c) ==> (G ^ ' a |= c)) /\
 (!G a c. (G ^ ' a ^ ' a |= c) ==> (G ^ ' a |= c)) /\
 (!G D a c. (G |= a) /\ (D ^ ' a |= c) ==> (G ^ D |= c)) /\


 (!G D a b. (G |= a) /\ (D |= b) ==> (G ^ D |= a % b)) /\
 (!G a b c. (G ^ ' a |= c) ==> (G ^ ' (a % b) |= c)) /\
 (!G a b c. (G ^ ' b |= c) ==> (G ^ ' (a % b) |= c)) /\

 (!G D a b c. (G ^ ' b |= c) /\ (D |= a) ==> (G ^ D ^ ' (a --> b) |= c)) /\
 (!G a b. (G ^ ' a |= b) ==> (G |= (a --> b)))
` ;;


(*let prop_RULES,prop_INDUCT,prop_CASES = new_inductive_definition 
`(!G a. G ^ ' a |= a) /\
 (!G. G |= Truth) /\
 (!G a b. G ^ ' a ^ ' b |= a % b) /\
 (!G a b. G ^ '(a % b) |= a) /\
 (!G a b. G ^ '(a % b) |= b) /\
 (!G a b. (G ^ ' (a --> b) ^ ' a) |= b) /\
 (!G a b. ((G ^ ' a) |= b) ==> (G |= (a --> b))) 
` ;;
*)


(* Split the rules to be used as meta-rules! *)

let [pID;
     pW; pC; pCut; 
     pXR; pXL1; pXL2;
     pIL; pIR
   ] = 
  map (MIMP_RULE o SPEC_ALL o REWRITE_RULE[IMP_CONJ]) 
    (CONJUNCTS propRULES);;
  


g `mempty |= X % Y --> Y % X` ;;
eseq (ruleseq pIR);;
eseq (ruleseq pC);;
eseq (ruleseq pXR);;
eseq (ruleseq pXL2);;
eseq (ruleseq pID);;
eseq (ruleseq pXL1);;
eseq (ruleseq pID);;

top_thm();;


let lamINDUCT,lamRECURSION = define_type
    " Lambda = Var A
     | App Lambda Lambda
     | Prod (Lambda#Lambda)
     | Lam A Lambda
";;

parse_as_infix("@@",(10,"right"));; 
override_interface("@@",`App`);;


let lamFst_DEF = new_recursive_definition lamRECURSION 
                `Fst (Prod x :(A)Lambda) = FST x` ;; 

let lamFst = prove (`!x y. Fst (Prod (x,y)) = x`, REWRITE_TAC[lamFst_DEF;FST]);;


let lamSnd_DEF = new_recursive_definition lamRECURSION 
                `Snd (Prod x :(A)Lambda) = SND x` ;; 

let lamSnd = prove (`!x y. Snd (Prod (x,y)) = y`, REWRITE_TAC[lamSnd_DEF;SND]);;



(* Annotating terms with types. *)

let tmINDUCT,tmRECURSION = define_type "TTerm = Annotate A Prop";;

parse_as_infix("::",(16,"right"));;
override_interface("::",`Annotate`);;


(* Printer to hide terms from proofs. *)

let chTermString tm =
  try 
    let c,args = strip_comb tm in
    let op = (fst o dest_const) c in
    if (String.equal op "Annotate") 
    then (string_of_term o hd o tl) args 
    else failwith ""
  with Failure _ -> failwith "Not a Curry-Howard term."

let print_chTerm fmt = pp_print_string fmt o chTermString

let hide_lam,show_lam =
  (fun () -> install_user_printer ("print_chTerm",print_chTerm)),
  (fun () -> try delete_user_printer "print_chTerm"
             with Failure _ -> failwith ("show_procs: " ^
                                           "Curry-Howard lambda terms are already being shown normally."));;
    
hide_lam();;



(* Consequence operator *)
parse_as_infix("|==",(11,"right"));;

let chRULES,chINDUCT,chCASES = new_inductive_definition 
`(!a x. ' (x :: a) |== x :: a) /\

 (!G a c x z. (G |== z :: c) ==> (G ^ ' (x :: a) |== z :: c)) /\
 (!G a c x z. (G ^ '(x :: a) ^ '(x :: a) |== z :: c) ==> (G ^ ' (x :: a) |== z :: c)) /\
 (!G D a c x z. (G |== z :: a) /\ (D ^ ' (z :: a) |== x :: c) ==> (G ^ D |== x :: c)) /\


 (!G D a b x y. (G |== x :: a) /\ (D |== y :: b) ==> (G ^ D |== Prod (x,y) :: (a % b))) /\
 (!G a b c x. (G ^ ' (Fst x :: a) |== c) ==> (G ^ ' (x :: (a % b)) |== c)) /\
 (!G a b c x. (G ^ ' (Snd x :: b) |== c) ==> (G ^ ' (x :: (a % b)) |== c)) /\

 (!G D a b c f y z. (G ^ ' ((f @@ y) :: b) |== z :: c) /\ (D |== (y :: a)) ==> (G ^ D ^ ' (f :: (a --> b)) |== z :: c)) /\
 (!G a b x y. (G ^ ' (Var x :: a) |== (y :: b)) ==> (G |== Lam x y :: (a --> b)))
` ;;

let [chID;
     chW; chC; chCut; 
     chXR; chXL1; chXL2;
     chIL; chIR
   ] = 
  map (MIMP_RULE o SPEC_ALL o REWRITE_RULE[IMP_CONJ]) 
    (CONJUNCTS chRULES);;
;;

g `?P:(num)Lambda. mempty |== P :: (X % Y --> Y % X)` ;;
e (META_EXISTS_TAC);;
eseq (ruleseq chIR);;
eseq (ruleseq chC);;
eseq (ruleseq chXR);;
eseq (ruleseq chXL2);;
eseq (ruleseq chID);;
eseq (ruleseq chXL1);;
eseq (ruleseq chID);;

top_thm();;
instantiate (top_inst(p())) `P:(num)Lambda` ;;
let xp = it;;



(*


(* Some theorems: *)
let TIMES_COMM = prove_seq( `'(b**a) |= a ** b`,
					    EEVERY [
					    ruleseq ill_timesL;
					    rule_seqtac [`G`,`' a`] ill_timesR;
					    ruleseq ill_id]);;

let illtimes_commR = prove_seq (`G |= b ** a ===> G |= a ** b`,
				ETHENL (EEVERY [
				  ETAC (MIMP_TAC THEN DISCH_TAC);
				  drule_seqtac [`c`,`a ** b`;`D`,`mempty:(ILinProp)multiset`] ill_cut]) [
				  ETAC (MATCH_ACCEPT_TAC TIMES_COMM);
				  ETAC assumption]);;

let illtimes_commL = prove_seq (`G ^ ' (a ** b) |= c ===> G ^ ' (b ** a) |= c`,
				ETHENL (EEVERY [
				  ETAC (MIMP_TAC THEN DISCH_TAC);
				  rule_seqtac [`a`,`a ** b`;`G`,`' (b ** a)`] ill_cut]) [
				  ETAC (MATCH_ACCEPT_TAC TIMES_COMM);
				  ETAC assumption]);;


(* Now we can use these as new rules! *)

prove_seq (`' ((A ** B)** C) |= (C ** (B ** A))`,
	   EEVERY [
	     ruleseq illtimes_commR;
	     ruleseq ill_timesL;
	     ETHENL (rule_seqtac [`D`,`' C`] ill_timesR)
	     [ ruleseq illtimes_commR ; ruleseq ill_id ];
	     ruleseq ill_id]);;


let TIMES_ASSOC_L = prove_seq (`' ((a ** b) ** c) |= a ** (b ** c)`,
			       EEVERY [
				 EREPEAT (ruleseq ill_timesL);
				 ETHENL (rule_seqtac [`G`,`' a`] ill_timesR) 
				   [ ruleseq ill_id ; rule_seqtac [`G`,`' b`] ill_timesR ];
				 ruleseq ill_id]);;

let TIMES_ASSOC_R = prove_seq ( `' (a ** (b ** c)) |= (a ** b) ** c`,
				EEVERY [
				  EREPEAT (ruleseq ill_timesL); 
				  ETHENL (rule_seqtac [`G`,`' a ^ ' b`] ill_timesR)
				    [ ruleseq ill_timesR ; ruleseq ill_id ];
				  ruleseq ill_id]);;

let ONE_TIMES_L = prove_seq (`' (IOne ** a) |= a`,
			     EEVERY [
			       ruleseq ill_timesL;
			       ruleseq ill_oneL;
			       ruleseq ill_id]);;

let ONE_TIMES_R = prove_seq (`' (a ** IOne) |= a`,
		     	     EEVERY [
			       ruleseq ill_timesL;
			       ruleseq ill_oneL;
			       ruleseq ill_id]);;

let PLUS_COMM = prove_seq (`' (b ++ a) |= a ++ b`,
		      ETHEN
			(ETHENL (ruleseq ill_plusL) [ ruleseq ill_plusR2 ; ruleseq ill_plusR1 ])
			(ruleseq ill_id));;

let PLUS_A_A = prove_seq (`' (a ++ a) |= a`,
		     ETHEN (ruleseq ill_plusL) (ruleseq ill_id));;

let OFC_WITH_EQ_TIMES = prove_seq (`' (!!(a && b)) |= (a ** b)`,
				   ETHEN (ETHENL (EEVERY [
				     ruleseq ill_ofcC;
				     ruleseq ill_timesR;
				     ruleseq ill_ofcL])
				     [ruleseq ill_withL1 ; ruleseq ill_withL2])
				     (ruleseq ill_id));;

let IMP_IMP_EQ_TIMES = prove_seq (`' (a-->(b-->c)) |= (a**b)-->c`,
  EEVERY [
    ruleseq ill_impR;
    ruleseq ill_timesL;
    ruleseq ill_impL;
    ETRY (ruleseq ill_id);
    rule_seqtac [`G`,`' b`] ill_impL;
    ruleseq ill_id]);;

let TIMES_EQ_IMP_IMP = prove_seq (`' ((a**b)-->c) |= a-->(b-->c)`,
  EEVERY [
    EREPEAT (ruleseq ill_impR);
    ETHENL (rule_seqtac [`G`,`' a ^ ' b`] ill_impL)
      [ ruleseq ill_timesR ; ruleseq ill_id ];
    ruleseq ill_id]);;

prove_seq (`' d ^ ' ((a**c) --> b) ^ ' a ^ ' d ^ ' c |= (b**d**d)`,
	   EEVERY [
	     ETHENL (rule_seqtac [`D`,`' d ^ ' d`] ill_timesR)
	       [ rule_seqtac [`G`,`' a ^ ' c`] ill_impL ; ruleseq ill_timesR ];
	   EORELSE (ruleseq ill_timesR) (ruleseq ill_id);
	   ruleseq ill_id]);;

*)
