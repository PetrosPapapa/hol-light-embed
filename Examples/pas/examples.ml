(* ========================================================================= *)
(* Example proofs for Propositions-as-Sessions.                              *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                 2012-2019                                 *)
(* ========================================================================= *)

needs "embed/LL/pas/pas.ml";;

(* Interactive construction proof of commutativity of tensor. *)
g `?P w x. |-- (' (w <> (NEG (A ** B))) ^ '(x <> (B ** A))) P` ;;
e (REPEAT META_EXISTS_TAC THEN REWRITE_TAC[NEG_CLAUSES]);;
eseq (ruleseq ll_par);;
eseq (rule_seqtac [`G`,`'(w <> NEG B)`] ll_times);;
eseq (ruleseq ll_id);;
eseq (ruleseq ll_id);;
top_thm();;
instantiate (top_inst (p())) `P:CProc`;;
print_cp (instantiate (top_inst (p())) `P:CProc` );; (* Pretty printing *)

(* Packaged verification proof of commutativity of tensor. *)
let CP_TIMES_COMM = prove_seq (`|-- (' (w <> (NEG (A ** B))) ^ '(x <> (B ** A)))
    (In w y (Out x z (w <-> z) (y <-> x)))`, EEVERY [
      ETAC (REWRITE_TAC[NEG_CLAUSES]);
      ruleseq ll_par;
      rule_seqtac [`G`,`'(w <> NEG B)`] ll_times;
      ruleseq ll_id]);;


(* Interactive construction proof of a (A ** B) ++ (C ** D) buffer using BUFFER_ETAC. *)
g `?P w x. |-- (' (w <> (NEG ((A ** B) ++ (C ** D)))) ^ '(x <> ((A ** B) ++ (C ** D)))) P` ;;
e (REPEAT META_EXISTS_TAC);;
eseq (BUFFER_ETAC);;
top_thm();;
instantiate (top_inst (p())) `P:CProc` ;;

(* Interactive construction proof of commutativity of plus using CLL_TAC. *)
g `?P w x. |-- (' (w <> (NEG (A ++ B))) ^ '(x <> (B ++ A))) P` ;;
e (REPEAT META_EXISTS_TAC);;
eseq (CLL_TAC);;
top_thm();;
instantiate (top_inst (p())) `P:CProc` ;;

(* Packaged verification proof of commutativity of plus using CLL_TAC. *)
let CP_PLUS_COMM = prove_seq (`|-- (' (w <> (NEG (A ++ B))) ^ '(x <> (B ++ A)))
   (Case w (Inr x (w <-> x)) (Inl x (w <-> x)))`, CLL_TAC);;

(* Interactive construction proof of (left) distributivity of times over plus using CLL_TAC. *)
g `?P w x. |-- (' (w <> (NEG (A ** (B ++ C)))) ^ '(x <> ((A ** B) ++ (A ** C)))) P` ;;
e (REPEAT META_EXISTS_TAC);;
eseq (CLL_TAC);;
instantiate (top_inst (p())) `P:CProc` ;;

(* Packaged verification proof of (left) distributivity of times over plus using CLL_TAC. *)
let CP_DISTRIB = prove_seq (`|-- (' (w <> (NEG (A ** (B ++ C)))) ^ '(x <> ((A ** B) ++ (A ** C))))
    (In w xa (Case w (Inl x (Out x xb (xa <-> xb) (w <-> x))) (Inr x (Out x xc (xa <-> xc) (w <-> x)))))`,
    CLL_TAC);;

