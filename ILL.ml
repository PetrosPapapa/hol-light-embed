(* ========================================================================= *)
(* Deep embedding of Intuitionistic Linear Logic                             *)
(*                                                                           *)
(* Petros Papapanagiotou, Jacques Fleuriot                                   *)
(* Center of Intelligent Systems and their Applications                      *)
(* University of Edinburgh                                                   *)
(* 2017 - 2019                                                               *)
(* ========================================================================= *)

(* Dependencies *)
loads ("tools/embed.ml");;

(* Type declaration *)

let ilinprop_INDUCT,ilinprop_RECURSION = define_type
    "ILinProp = IOne
              | IOfCourse ILinProp
              | ILinImp ILinProp ILinProp
              | ILinWith ILinProp ILinProp
              | ILinPlus ILinProp ILinProp
              | ILinTimes ILinProp ILinProp";;

(* Pretty printing abbreviations *)

parse_as_infix("-->",(14,"right"));;
override_interface("-->",`ILinImp`);;
make_overloadable "&&" `:A->A->A`;;
parse_as_infix("&&",(13,"right"));;
overload_interface("&&",`ILinWith`);;
make_overloadable "++" `:A->A->A`;;
parse_as_infix("++",(13,"right"));;
overload_interface("++",`ILinPlus`);;
make_overloadable "**" `:A->A->A`;;
parse_as_infix("**",(13,"right"));;
overload_interface("**",`ILinTimes`);;
make_overloadable "!!" `:A->A`;;
parse_as_prefix("!!");;
overload_interface("!!",`IOfCourse`);;

(* Some automatically proven properties *)

let ilinprop_CASES = prove_cases_thm ilinprop_INDUCT;;
	      
let ilinprop_DISTINCT = distinctness "ILinProp";;

let ilinprop_INJ = injectivity "ILinProp";;

(* Linear consequence *)
parse_as_infix("|=",(11,"right"));;

let ilinear_RULES,ilinear_INDUCT,ilinear_CASES = new_inductive_definition
`(!a. ' a |= a) /\
 (mempty |= IOne) /\
 (!a G. (G |= a) ==> ( G ^ ' IOne |= a )) /\
 (!a b c G. ((G ^ ' a ^ ' b) |= c) ==> ( (G ^ ' (a ** b)) |= c)) /\
 (!a b G D. (G |= a) /\ (D |= b) ==> ( (G ^ D) |= (a ** b))) /\
 (!a b c G D. (G |= a) /\ (D ^ ' b |= c) ==> (G ^ D ^ '(a --> b) |= c)) /\
 (!a b G. ( G ^ ' a |= b ) ==> ( G |= (a --> b) )) /\
 (!a b d G. (G ^ ' a |= d) /\ (G ^ ' b |= d) ==> ((G ^ '(a ++ b)) |= d)) /\
 (!a b G. (G |= a) ==> (G |= (a ++ b))) /\
 (!a b G. (G |= b) ==> (G |= (a ++ b))) /\
 (!a b d G. (G ^ ' a |= d) ==> (G ^ ' (a && b)) |= d) /\
 (!a b d G. (G ^ ' b |= d) ==> (G ^ ' (a && b)) |= d) /\
 (!a b G. (G |= a) /\ (G |= b) ==> (G |= (a && b))) /\
 (!a d G. (G |= d) ==> ((G ^ ' (!!a)) |= d)) /\
 (!a d G. (G ^ ' a |= d) ==> ((G ^ ' (!!a)) |= d)) /\
 (!a d G. (G ^ ' (!!a) ^ ' (!!a) |= d) ==> ((G ^ ' (!!a)) |= d)) /\
 (!a c G D. (G |= a) /\ (D ^ ' a |= c) ==> (G ^ D |= c))
`;;

(* Split the rules to be used as IsaHOL rules! *)

let [ill_id;
     ill_oneR;ill_oneL;
     ill_timesL;ill_timesR;
     ill_impL;ill_impR;
     ill_plusL;ill_plusR1;ill_plusR2;
     ill_withL1; ill_withL2; ill_withR;
     ill_ofcW; ill_ofcL; ill_ofcC;
     ill_cut
   ] = 
  map (MIMP_RULE o SPEC_ALL o REWRITE_RULE[IMP_CONJ]) 
    (CONJUNCTS ilinear_RULES);;
  

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

