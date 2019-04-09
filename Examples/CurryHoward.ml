(* ========================================================================= *)
(* Shallow embedding of a subset of propositional logic and the Curry-Howard *)
(* isomoprhism.                                                              *)
(*                                                                           *)
(* Petros Papapanagiotou                                                     *)
(* Center of Intelligent Systems and their Applications                      *)
(* University of Edinburgh                                                   *)
(* 2019                                                                      *)
(* ------------------------------------------------------------------------- *)
(* This includes the rules of a subset of propositional logic and its 
   a formulation of the Curry-Howard isomorphism for that subset.

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
     pX_R; pX_L1; pX_L2;
     pI_L; pI_R
   ] = 
  map (MIMP_RULE o SPEC_ALL o REWRITE_RULE[IMP_CONJ]) 
    (CONJUNCTS propRULES);;
  


g `mempty |= X % Y --> Y % X` ;;
eseq (ruleseq pI_R);;
eseq (ruleseq pC);;
eseq (ruleseq pX_R);;
eseq (ruleseq pX_L2);;
eseq (ruleseq pID);;
eseq (ruleseq pX_L1);;
eseq (ruleseq pID);;

top_thm();;



(* ------------------------------------------------------------------------- *)
(* Curry-Howard correspondence                                               *)
(* ------------------------------------------------------------------------- *)

(* Lambda terms *)

let lamINDUCT,lamRECURSION = define_type
    " Lambda = Var A
     | App Lambda Lambda
     | Prod (Lambda#Lambda)
     | Lam A Lambda
";;

(* Application syntax sugar  *)
parse_as_infix("@@",(10,"right"));; 
override_interface("@@",`App`);;


(* Projection functions for products *)

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
    

(* Hiding by default. Use "show_lam();;" to disable. *)
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
     chX_R; chX_L1; chX_L2;
     chI_L; chI_R
   ] = 
  map (MIMP_RULE o SPEC_ALL o REWRITE_RULE[IMP_CONJ]) 
    (CONJUNCTS chRULES);;
;;


(* Extract lambda term in a construction proof. *)

let lamConstruct p st = 
  let construct m =
    if (String.equal p ((fst o dest_var) m)) 
    then instantiate (top_inst st) m
    else failwith "Not found!" in
  tryfind construct (top_metas st);;

let top_constr s = lamConstruct s (p());;


(* Shorthand for an empty context *)
let chEmpty ty = inst [ty,`:A`] `mempty:(((A)Lambda)TTerm)multiset` ;;


(* ------------------------------------------------------------------------- *)
(* Example proofs                                                            *) 
(* ------------------------------------------------------------------------- *)

(* Construct a function that swaps products around.                          *)

g `?P:(num)Lambda. mempty |== P :: (X % Y --> Y % X)` ;;
e (META_EXISTS_TAC);;
eseq (ruleseq chI_R);; (* implication R *)
eseq (ruleseq chC);; (* contraction *)
eseq (ruleseq chX_R);; (* conjunction R *)
eseq (ruleseq chX_L2);; (* conjunction L2 *)
eseq (ruleseq chID);; (* identity *)
eseq (ruleseq chX_L1);; (* conjunction L1 *)
eseq (ruleseq chID);; (* identity *)

top_thm();; (* Validates the entire proof and reconstructs the theorem. *)
top_constr "P";; (* Gives: Lam x0 (Prod (Snd (Var x0),Fst (Var x0))) *)


(* Verification proof for the same term.                                     *)
(* i.e. Does this function have the right type?                              *)

g `mempty |== Lam x (Prod (Snd (Var x),Fst (Var x))) :: (X % Y --> Y % X)` ;;
eseq (ruleseq chI_R);;
eseq (ruleseq chC);;
eseq (ruleseq chX_R);;
eseq (ruleseq chX_L2);;
eseq (ruleseq chID);;
eseq (ruleseq chX_L1);;
eseq (ruleseq chID);;

top_thm();;


(* 
From the proof perspective, we are looking at commutativity of conjunction. 
We want a lemma that we can use as a rule in future proofs.  
*)

(* 
First we need to construct the corresponding lambda terms to make a valid rule.
*)

g `?a b. ' (a :: (X % Y)) |== b :: (Y % X)` ;;
e (REPEAT META_EXISTS_TAC);;
eseq (ruleseq chC);;
eseq (ruleseq chX_R);;
eseq (ruleseq chX_L2);;
eseq (ruleseq chID);;
eseq (ruleseq chX_L1);;
eseq (ruleseq chID);;
top_thm();;
top_constr "a";; (* Gives: a *)
top_constr "b";; (* Gives: Prod (Snd a,Fst a) *)

(* 
These are not the only possible terms, but they are valid. 
We did not use any cuts so we are fine.
We need meta-theory (cut elimination) to formally prove they are minimal terms in general.
*)

(*
Now we can construct a reusable lemma by packaging the proof.
*)

let TIMES_COMM = prove_seq( `' (a :: (X % Y)) |== Prod (Snd a, Fst a) :: (Y % X)`,
                                            ETHENL 
                                              (ETHEN (ruleseq chC) (ruleseq chX_R))
                                              [
                                                ETHEN (ruleseq chX_L2) (ruleseq chID);
                                                ETHEN (ruleseq chX_L1) (ruleseq chID) ]
);;
           

(* 
Using TIMES_COMM we want to be able to manipulate terms in a sequent.
This can be accomplished by a more general lemma with a variable context G. 
Once again we start with the construction proof to obtain valid lambda terms. 
*)

g `?a:(A)Lambda b. G |== a :: (X % Y) ===> G |== b :: (Y % X)` ;;
e (REPEAT META_EXISTS_TAC);;
e (MDISCH_TAC);;
eseq (drule_seqtac [`c`,`Y % X`;`D`,chEmpty `:A`] chCut);; (* cut! *)
eseq (ruleseq TIMES_COMM);; (* Using the lemma we proved earlier *)
eseq (seqassumption);;
top_thm();;
top_constr "a";; (* Gives: a *)
top_constr "b";; (* Gives: Prod (Snd a,Fst a) *)

(*
And now we package the proof and our lemma is ready to use. 
*)
let chTimesCommR = prove_seq (`G |== a:(A)Lambda :: (X % Y) ===> G |== Prod (Snd a,Fst a) :: (Y % X)`,
				ETHENL ( ETHEN
				  (ETAC (MDISCH_TAC))
				  (drule_seqtac [`c`,`Y % X`;`D`,chEmpty `:A`] chCut) ) [
				  ruleseq TIMES_COMM;
				  seqassumption]);;

(*
We prove a similar lemma that allows us to manipulate terms on the left hand side of the sequent.
*)
g `?a:(A)Lambda b. G ^ ' (a :: (X % Y)) |== z :: C  ===> G ^ ' (b :: (Y % X)) |== z :: C` ;;
e (REPEAT META_EXISTS_TAC);;
e (MDISCH_TAC);;
eseq (rule_seqtac [`a`,`X % Y`;`G`,`' (b :: (Y % X))`] chCut);;
eseq (ruleseq TIMES_COMM);;
eseq (seqassumption);;
top_thm();;
top_constr "a";;
top_constr "b";;

let chTimesCommL = prove_seq (`G ^ ' (Prod (Snd a,Fst a) :: (X % Y)) |== z :: C  ===> G ^ ' (a :: (Y % X)) |== z :: C`,
				ETHENL ( ETHEN
				  (ETAC (MDISCH_TAC))
				  (rule_seqtac [`a`,`X % Y`;`G`,`' (a :: (Y % X))`] chCut) ) [
				  ruleseq TIMES_COMM;
				  seqassumption]);;


(* 
Here is an example of how we can use these lemmas to manipulate terms in a proof.
*)

g `? P. mempty |== P :: (((A % B) % C) --> (C % (B % A)))` ;;
e (REPEAT META_EXISTS_TAC);;
eseq (ruleseq chI_R);;
eseq (ruleseq chTimesCommR);;
eseq (ruleseq chC);;
eseq (ruleseq chX_R);;

eseq (ruleseq chX_L1);;
eseq (ruleseq chTimesCommL);;
eseq (ruleseq chID);;

eseq (ruleseq chX_L2);;
eseq (ruleseq chID);;

top_thm();;
top_constr "P";; 
(* Gives: 
`Lam x0
   (Prod
   (Snd (Prod (Prod (Snd (Fst (Var x0)),Fst (Fst (Var x0))),Snd (Var x0))),
    Fst (Prod (Prod (Snd (Fst (Var x0)),Fst (Fst (Var x0))),Snd (Var x0)))))`
*)

(*
Some more proofs.

We can use this type of proof to construct more complex programs.
We put function and variable definitions (such as `a` here) in the context and 
give a type specification (such as `X --> Y --> Z` here) in the conclusion.
The proof will generate the program `b` for us.
*)

g `?b:(A)Lambda . ' (a :: (X % Y --> Z)) |== b :: (X --> Y --> Z)` ;;
e (REPEAT META_EXISTS_TAC);;
eseq (ruleseq chI_R);;
eseq (ruleseq chI_R);;
eseq (rule_seqtac [`G`, chEmpty `:A`] chI_L);;

eseq (ruleseq chID);;

eseq (ruleseq chX_R);;
eseq (ruleseq chID);;
eseq (ruleseq chID);;

top_thm();;
top_constr "b";; (* Gives: Lam x0 (Lam x1 (a @@ Prod (Var x0,Var x1))) *)


g `?b. ' (a :: (X--> Y-->Z)) |== b :: (X % Y --> Z)` ;;
e (REPEAT META_EXISTS_TAC);;
eseq (ruleseq chI_R);;
eseq (rule_seqtac [`a`,`X % Y`] chC);;
eseq (ruleseq chI_L);;
eseq (ruleseq chI_L);;

eseq (ruleseq chID);;

eseq (ruleseq chX_L2);;
eseq (ruleseq chID);;

eseq (ruleseq chX_L1);;
eseq (ruleseq chID);;

top_thm();;
top_constr "b";; (* Gives: Lam x0 ((a @@ Fst (Var x0)) @@ Snd (Var x0)) *)

