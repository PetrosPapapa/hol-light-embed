(* ========================================================================= *)
(* Deep embedding of Phil Wadler's CP (Classical Processes) calculus.        *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                2012 - 2019                                *)
(* ========================================================================= *)

(* Dependencies *)

needs "IsabelleLight/make.ml";;
needs "tools/Library/lists.ml";; 
needs "tools/Library/sets.ml";;
needs "tools/Library/substitution.ml";;
needs "tools/Library/fresh.ml";;

(* Type declaration *)

let cp_INDUCT,cp_RECURSION = define_type
    " CProcess = Link A A 
            | Par A B CProcess CProcess
            | Out A A CProcess CProcess
            | In A A CProcess
	    | Inl A CProcess
	    | Inr A CProcess
	    | Case A CProcess CProcess
	    | ROut A A CProcess
	    | RIn A A CProcess
	    | TOut A B CProcess
	    | TIn A B CProcess
	    | EOut A
	    | EIn A CProcess
	    | ECase A";;


parse_as_infix("<->",(11,"right"));; 
override_interface("<->",`Link`);;


let is_cp tm = try ( (fst o dest_type o type_of) tm = "CProcess" ) with Failure _ -> false;;
  

(* Induction tactic *)
(* TODO: Test + fix *)

let CP_INDUCT_TAC =
  MATCH_MP_TAC cp_INDUCT THEN
  CONJ_TAC THENL [ALL_TAC; GEN_ALL_TAC THEN DISCH_TAC];;


(* Injectivity theorem *)

let CP_INJ = injectivity "CProcess";;


(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Functions about names.                                                    *)
(* ------------------------------------------------------------------------- *)
(* We define two versions of these functions, one returning a set and one    *)
(* returning a list. We found lists to be generally easier to reason about   *)
(* in HOL Light.                                                             *)
(* We prove that the two definitions are equivalent.                         *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Free names.                                                               *)
(* ------------------------------------------------------------------------- *)


let FN_SET = new_recursive_definition cp_RECURSION 
 `(!x y. FNS (x <-> y) = {x,y}) /\
  (!x A P Q. FNS (Par x A P Q) = ((FNS P) UNION (FNS Q)) DIFF {x}) /\
  (!x y P Q. FNS (Out x y P Q) = {x} UNION ((FNS P) DIFF {y}) UNION (FNS Q)) /\
  (!x y P. FNS (In x y P) = {x} UNION ((FNS P) DIFF {y})) /\
  (!x P. FNS (Inl x P) = {x} UNION FNS P) /\
  (!x P. FNS (Inr x P) = {x} UNION FNS P) /\
  (!x P Q. FNS (Case x P Q) = {x} UNION (FNS P) UNION (FNS Q)) /\
  (!x y P. FNS (ROut x y P) = {x} UNION ((FNS P) DIFF {y})) /\
  (!x y P. FNS (RIn x y P) = {x} UNION ((FNS P) DIFF {y})) /\
  (!x A P. FNS (TOut x A P) = {x} UNION FNS P) /\
  (!x A P. FNS (TIn x A P) = {x} UNION FNS P) /\
  (!x. FNS (EOut x) = {x}) /\
  (!x P. FNS (EIn x P) = {x} UNION FNS P) /\
  (!x. FNS (ECase x) = {x})`;;


let FN = new_recursive_definition cp_RECURSION 
 `(!x y. FN (x <-> y) = [x;y]) /\
  (!x A P Q. FN (Par x A P Q) = (APPEND (FN P) (FN Q)) DEL x) /\
  (!x y P Q. FN (Out x y P Q) = CONS x (APPEND ((FN P) DEL y) (FN Q))) /\
  (!x y P. FN (In x y P) = CONS x ((FN P) DEL y)) /\
  (!x P. FN (Inl x P) = CONS x (FN P)) /\
  (!x P. FN (Inr x P) = CONS x (FN P)) /\
  (!x P Q. FN (Case x P Q) = CONS x (APPEND (FN P) (FN Q))) /\
  (!x y P. FN (ROut x y P) = CONS x ((FN P) DEL y)) /\
  (!x y P. FN (RIn x y P) = CONS x ((FN P) DEL y)) /\
  (!x A P. FN (TOut x A P) = CONS x (FN P)) /\
  (!x A P. FN (TIn x A P) = CONS x (FN P)) /\
  (!x. FN (EOut x) = [x]) /\
  (!x P. FN (EIn x P) = CONS x (FN P)) /\
  (!x. FN (ECase x) = [x])`;;

let FNS_EQ_FN = prove (`!P. FNS P = set_of_list (FN P)`,
		       MATCH_MP_TAC cp_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN 
			 REWRITE_TAC[FN;FN_SET;SET_OF_LIST_APPEND;SET_OF_LIST_DEL;set_of_list]
			 THEN (DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC) ORELSE DISCH_THEN SUBST1_TAC)	      	 
		       THEN SET_TAC[]);;


let mk_cp_fn tm = mk_icomb (`FN`,tm);;


(* ------------------------------------------------------------------------- *)
(* Bound names.                                                              *)
(* ------------------------------------------------------------------------- *)


let BN_SET = new_recursive_definition cp_RECURSION 
 `(!x y. BNS (x <-> y) = {}) /\
  (!x A P Q. BNS (Par x A P Q) = {x} UNION (BNS P) UNION (BNS Q)) /\
  (!x y P Q. BNS (Out x y P Q) = {y} UNION (BNS P) UNION (BNS Q)) /\
  (!x y P. BNS (In x y P) = {y} UNION (BNS P)) /\
  (!x P. BNS (Inl x P) = BNS P) /\
  (!x P. BNS (Inr x P) = BNS P) /\
  (!x P Q. BNS (Case x P Q) = (BNS P) UNION (BNS Q)) /\
  (!x y P. BNS (ROut x y P) = {y} UNION (BNS P)) /\
  (!x y P. BNS (RIn x y P) = {y} UNION (BNS P)) /\
  (!x A P. BNS (TOut x A P) = BNS P) /\
  (!x A P. BNS (TIn x A P) = BNS P) /\
  (!x. BNS (EOut x) = {}) /\
  (!x P. BNS (EIn x P) = BNS P) /\
  (!x. BNS (ECase x) = {})`;;

let BN = new_recursive_definition cp_RECURSION 
 `(!x y. BN (x <-> y) = []) /\
  (!x A P Q. BN (Par x A P Q) = CONS x (APPEND (BN P) (BN Q))) /\
  (!x y P Q. BN (Out x y P Q) = CONS y (APPEND (BN P) (BN Q))) /\
  (!x y P. BN (In x y P) = CONS y (BN P)) /\
  (!x P. BN (Inl x P) = BN P) /\
  (!x P. BN (Inr x P) = BN P) /\
  (!x P Q. BN (Case x P Q) = APPEND (BN P) (BN Q)) /\
  (!x y P. BN (ROut x y P) = CONS y (BN P)) /\
  (!x y P. BN (RIn x y P) = CONS y (BN P)) /\
  (!x A P. BN (TOut x A P) = BN P) /\
  (!x A P. BN (TIn x A P) = BN P) /\
  (!x. BN (EOut x) = []) /\
  (!x P. BN (EIn x P) = BN P) /\
  (!x. BN (ECase x) = [])`;;


let BNS_EQ_BN = prove (`!P. BNS P = set_of_list (BN P)`,
		       MATCH_MP_TAC cp_INDUCT THEN
		       REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN 
			 REWRITE_TAC[BN;BN_SET;SET_OF_LIST_APPEND;set_of_list] THEN 
			 (DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC) ORELSE DISCH_THEN SUBST1_TAC) 
			 THEN SET_TAC[]);;




let mk_cp_bn tm = mk_icomb (`BN`,tm);;



(* ------------------------------------------------------------------------- *)
(* All names.                                                                *)
(* ------------------------------------------------------------------------- *)

let NAMES_SET = new_recursive_definition cp_RECURSION 
 `(!x y. NAMESS (x <-> y) = {x,y}) /\
  (!x A P Q. NAMESS (Par x A P Q) = {x} UNION (NAMESS P) UNION (NAMESS Q)) /\
  (!x y P Q. NAMESS (Out x y P Q) = {x,y} UNION (NAMESS P) UNION (NAMESS Q)) /\
  (!x y P. NAMESS (In x y P) = {x,y} UNION (NAMESS P)) /\
  (!x P. NAMESS (Inl x P) = {x} UNION NAMESS P) /\
  (!x P. NAMESS (Inr x P) = {x} UNION NAMESS P) /\
  (!x P Q. NAMESS (Case x P Q) = {x} UNION (NAMESS P) UNION (NAMESS Q)) /\
  (!x y P. NAMESS (ROut x y P) = {x,y} UNION (NAMESS P)) /\
  (!x y P. NAMESS (RIn x y P) = {x,y} UNION (NAMESS P)) /\
  (!x A P. NAMESS (TOut x A P) = {x} UNION NAMESS P) /\
  (!x A P. NAMESS (TIn x A P) = {x} UNION NAMESS P) /\
  (!x. NAMESS (EOut x) = {x}) /\
  (!x P. NAMESS (EIn x P) = {x} UNION NAMESS P) /\
  (!x. NAMESS (ECase x) = {x})`;;

let NAMES = new_recursive_definition cp_RECURSION 
 `(!x y. NAMES (x <-> y) = [x;y]) /\
  (!x A P Q. NAMES (Par x A P Q) = CONS x (APPEND (NAMES P) (NAMES Q))) /\
  (!x y P Q. NAMES (Out x y P Q) = CONS x (CONS y (APPEND (NAMES P) (NAMES Q)))) /\
  (!x y P. NAMES (In x y P) = CONS x (CONS y (NAMES P))) /\
  (!x P. NAMES (Inl x P) = CONS x (NAMES P)) /\
  (!x P. NAMES (Inr x P) = CONS x (NAMES P)) /\
  (!x P Q. NAMES (Case x P Q) = CONS x (APPEND (NAMES P) (NAMES Q))) /\
  (!x y P. NAMES (ROut x y P) = CONS x (CONS y (NAMES P))) /\
  (!x y P. NAMES (RIn x y P) = CONS x (CONS y (NAMES P))) /\
  (!x A P. NAMES (TOut x A P) = CONS x (NAMES P)) /\
  (!x A P. NAMES (TIn x A P) = CONS x (NAMES P)) /\
  (!x. NAMES (EOut x) = [x]) /\
  (!x P. NAMES (EIn x P) = CONS x (NAMES P)) /\
  (!x. NAMES (ECase x) = [x])`;;


let NAMESS_EQ_NAMES = prove (`!P. NAMESS P = set_of_list (NAMES P)`,
		       MATCH_MP_TAC cp_INDUCT THEN
		       REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN 
			 REWRITE_TAC[NAMES;NAMES_SET;SET_OF_LIST_APPEND;set_of_list] THEN 
			 (DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC) ORELSE DISCH_THEN SUBST1_TAC) 
			 THEN SET_TAC[]);;


let mk_cp_names tm = mk_icomb (`NAMES`,tm);;


(* ------------------------------------------------------------------------- *)
(* Properties of sets of names.                                              *)
(* ------------------------------------------------------------------------- *)

let NAMESS_FNS_UNION_BNS = prove ( `!P. NAMESS P = (FNS P) UNION (BNS P)`, 
				MATCH_MP_TAC cp_INDUCT THEN REWRITE_TAC[NAMES_SET;BN_SET;FN_SET;UNION_EMPTY;UNION_ASSOC]
				  THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN 
				  (DISCH_THEN SUBST1_TAC ORELSE DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC)) 
				  THEN SET_TAC[]);;

let FINITE_FNS = prove (`!P . FINITE (FNS P)`, REWRITE_TAC[FNS_EQ_FN;FINITE_SET_OF_LIST]);;

let FINITE_BNS = prove (`!P . FINITE (BNS P)`, REWRITE_TAC[BNS_EQ_BN;FINITE_SET_OF_LIST]);;

let FINITE_NAMESS = prove (`!P . FINITE (NAMESS P)`, REWRITE_TAC[NAMESS_EQ_NAMES;FINITE_SET_OF_LIST]);;


(* ------------------------------------------------------------------------- *)
(* Properties of lists of names.                                             *)
(* ------------------------------------------------------------------------- *)

let NAME_BN_OR_FN = prove (`!P:(A,B)CProcess x:A. MEM x (NAMES P) <=> (MEM x (BN P)) \/ (MEM x (FN P))`, 
			   GEN_ALL_TAC THEN EQ_TAC THEN SPEC_TAC (`P:(A,B)CProcess`,`P:(A,B)CProcess`) THEN 
			     MATCH_MP_TAC cp_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN 
			     REWRITE_TAC[NAMES;BN;FN;MEM;MEM_APPEND;MEM_DEL] THEN MESON_TAC[]);;

let NON_NAME_FN = prove(`!x P. ~(MEM x (NAMES P)) ==> ~(MEM x (FN P))`, GEN_ALL_TAC THEN REWRITE_TAC[NAME_BN_OR_FN;DE_MORGAN_THM] THEN 
			  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC ACCEPT_TAC));;

let NON_NAME_BN = prove(`!x P. ~(MEM x (NAMES P)) ==> ~(MEM x (BN P))`, GEN_ALL_TAC THEN REWRITE_TAC[NAME_BN_OR_FN;DE_MORGAN_THM] THEN 
			  DISCH_THEN (CONJUNCTS_THEN2 ACCEPT_TAC ASSUME_TAC));;


(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Polyadic pi-calculus substitution.                                        *)
(* ------------------------------------------------------------------------- *)

let cpSUB = new_recursive_definition cp_RECURSION 
 `(!ch s x y. cpSUB ch (x <-> y) s = (SUB s x <-> SUB s y)) /\
  (!ch s x A P Q. cpSUB ch (Par x A P Q) s =
      let vs = MAP (SUB s) (APPEND (FN P) (FN Q) DEL x) in
      let x' = if (MEM x vs) then ch x vs else x in
      let s' = FEMPTY |+ (x,x') in
      Par (SUB s x) A (cpSUB ch P (FUNION s' s)) (cpSUB ch Q (FUNION s' s))) /\
  (!ch s x y P Q. cpSUB ch (Out x y P Q) s = 
      let vs = MAP (SUB s) ((FN P) DEL y) in
      let y' = if (MEM y vs) then ch y vs else y in
      let s' = FEMPTY |+ (y,y') in
      Out (SUB s x) y' (cpSUB ch P (FUNION s' s)) (cpSUB ch Q s)) /\
  (!ch s x y P. cpSUB ch (In x y P) s = 
      let vs = MAP (SUB s) ((FN P) DEL y) in
      let y' = if (MEM y vs) then ch y vs else y in
      let s' = FEMPTY |+ (y,y') in
      In (SUB s x) y' (cpSUB ch P (FUNION s' s))) /\
  (!ch s x P. cpSUB ch (Inl x P) s = Inl (SUB s x) (cpSUB ch P s)) /\
  (!ch s x P. cpSUB ch (Inr x P) s = Inr (SUB s x) (cpSUB ch P s)) /\
  (!ch s x P Q. cpSUB ch (Case x P Q) s = Case (SUB s x) (cpSUB ch P s) (cpSUB ch Q s)) /\
  (!ch s x y P. cpSUB ch (ROut x y P) s = 
      let vs = MAP (SUB s) ((FN P) DEL y) in
      let y' = if (MEM y vs) then ch y vs else y in
      let s' = FEMPTY |+ (y,y') in
      ROut (SUB s x) y' (cpSUB ch P (FUNION s' s))) /\
  (!ch s x y P. cpSUB ch (RIn x y P) s = 
      let vs = MAP (SUB s) ((FN P) DEL y) in
      let y' = if (MEM y vs) then ch y vs else y in
      let s' = FEMPTY |+ (y,y') in
      RIn (SUB s x) y' (cpSUB ch P (FUNION s' s))) /\
  (!ch s x A P. cpSUB ch (TOut x A P) s = TOut (SUB s x) A (cpSUB ch P s)) /\
  (!ch s x A P. cpSUB ch (TIn x A P) s = TIn (SUB s x) A (cpSUB ch P s)) /\
  (!ch s x. cpSUB ch (EOut x) s = EOut (SUB s x)) /\
  (!ch s x P. cpSUB ch (EIn x P) s = EIn (SUB s x) (cpSUB ch P s)) /\
  (!ch s x. cpSUB ch (ECase x) s = ECase (SUB s x))`;;

  
let is_cpSUB tm = 
  try ((is_strcomb "cpSUB" o rator o rator o rator) tm)
  with Failure _ -> false;;


(* ------------------------------------------------------------------------- *) 
(* Single name substitution.                                                 *)
(* ------------------------------------------------------------------------- *) 
(* This is for convenience.                                                  *)
(* ------------------------------------------------------------------------- *) 

let cpSUB1 = new_definition `!ch P x y. cpSUB1 ch P (x,y) = cpSUB ch P (FEMPTY |+ (x,y))`;;
			  


(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Pretty printing function using the original notation.                     *)
(* ------------------------------------------------------------------------- *)

let rec cp_string tm =
  if (is_cp tm) then
    if (is_var tm) then (fst o dest_var) tm 
    else 
      let comb,args = strip_comb tm in
      let combs = try (fst o dest_const) comb with Failure _ -> "" in 
      if ( combs = "Link" ) then ((string_of_term (hd args)) ^ "<->" ^ ((string_of_term o hd o tl) args))
      else if ( combs = "Par" ) then ("v " ^ (string_of_term (hd args)) ^ 
				      ":(" ^ ((string_of_term o hd o tl) args) ^ 
				      ")(" ^ ((cp_string o hd o tl o tl) args) ^
				      " | " ^ ((cp_string o hd o tl o tl o tl) args) ^ ")")
      else if ( combs = "Out" ) then ((string_of_term (hd args)) ^ 
				      "[" ^ ((string_of_term o hd o tl) args) ^
				      "].(" ^ ((cp_string o hd o tl o tl) args) ^
				      " | " ^ ((cp_string o hd o tl o tl o tl) args) ^ ")")
      else if ( combs = "In" ) then ((string_of_term (hd args)) ^ 
				     "(" ^ ((string_of_term o hd o tl) args) ^
				     ")." ^ ((cp_string o hd o tl o tl) args))
      else if ( combs = "Inl" ) then ((string_of_term (hd args)) ^ 
				      "[inl]." ^ ((cp_string o hd o tl) args))
      else if ( combs = "Inr" ) then ((string_of_term (hd args)) ^ 
				      "[inr]." ^ ((cp_string o hd o tl) args))
      else if ( combs = "Case" ) then ((string_of_term (hd args)) ^ 
				       ".case(" ^ ((cp_string o hd o tl) args) ^
				       "," ^ ((cp_string o hd o tl o tl) args) ^ ")")
      else if ( combs = "ROut" ) then ("?" ^ (string_of_term (hd args)) ^ 
				       "[" ^ ((string_of_term o hd o tl) args) ^
				       "]." ^ ((cp_string o hd o tl o tl) args))
      else if ( combs = "RIn" ) then ("!" ^ (string_of_term (hd args)) ^ 
				      "(" ^ ((string_of_term o hd o tl) args) ^
				      ")." ^ ((cp_string o hd o tl o tl) args))
      else if ( combs = "TOut" ) then ((string_of_term (hd args)) ^ 
				       "[" ^ ((string_of_term o hd o tl) args) ^
				       "]." ^ ((cp_string o hd o tl o tl) args))
      else if ( combs = "TIn" ) then ((string_of_term (hd args)) ^ 
				      "(" ^ ((string_of_term o hd o tl) args) ^
				      ")." ^ ((cp_string o hd o tl o tl) args))
      else if ( combs = "EOut" ) then ((string_of_term (hd args)) ^ "[].0")
      else if ( combs = "EIn" ) then ((string_of_term (hd args)) ^ "()." ^ 
				      ((cp_string o hd o tl) args))
      else if ( combs = "ECase" ) then ((string_of_term (hd args)) ^ ".case()")
      else if ( is_const comb or is_var comb) then ("(" ^ (string_of_term tm) ^ ")")
      else failwith ("nop!" ^ (string_of_term comb) ^ ":" ^ (string_of_type (type_of comb))) else failwith "noop!";;

let print_cp tm = (print_string o cp_string) tm;;
(* install_user_printer ("print_cp",print_cp);; *)

(*
let x  = `In 1 2 (Case 13 (3 <-> x) (RIn 4 y (Par 5 A (EIn 6 (ECase 7)) (Inl 8 (Inr 9 (Out 10 11 (z <-> j) (EOut 12)))))))`;;
print_string (cp_string x);;
*)

