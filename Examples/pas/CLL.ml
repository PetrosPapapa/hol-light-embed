(* ========================================================================= *)
(* Deep embedding of Classical Linear Logic                                  *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                 2009-2019                                 *)
(* ========================================================================= *)

(* Dependencies *)

needs "IsabelleLight/make.ml";;
needs "tools/make.ml";;

(* ------------------------------------------------------------------------- *)
(* Formalisation of Classical Propositional Linear Logic                     *)
(* ------------------------------------------------------------------------- *)

(* Type definition: Propositional Linear Logic term. *)

let linprop_INDUCT,linprop_RECURSION = define_type
    "LinProp = LinOne
              | Bottom
	      | Top
	      | LinZero
              | OfCourse LinProp
              | WhyNot LinProp
              | LinPlus LinProp LinProp
              | LinWith LinProp LinProp
              | LinTimes LinProp LinProp
              | LinPar LinProp LinProp"
;;


(* Pretty printing abbreviations *)

make_overloadable "++" `:A->A->A`;;
parse_as_infix("++",(13,"right"));; 
overload_interface("++",`LinPlus`);;
make_overloadable "**" `:A->A->A`;;
parse_as_infix("**",(13,"right"));;
overload_interface("**",`LinTimes`);;
make_overloadable "&&" `:A->A->A`;;
parse_as_infix("&&",(13,"right"));;
overload_interface("&&",`LinWith`);;
parse_as_infix("%",(13,"right"));;
override_interface("%",`LinPar`);;
make_overloadable "!!" `:A->A`;;
parse_as_prefix("!!");;
overload_interface("!!",`OfCourse`);;
parse_as_prefix("??");;
override_interface("??",`WhyNot`);;

let is_tensor = is_binary "LinTimes";;
let is_plus = is_binary "LinPlus";;
let is_par = is_binary "LinPar";;
let is_with = is_binary "LinWith";;

let flat_tensor = flat_binary "LinTimes";;
let flat_plus = flat_binary "LinPlus";;
let flat_par = flat_binary "LinPar";;
let flat_with = flat_binary "LinWith";;


(* Some automatically proven properties *)

let linear_CASES = prove_cases_thm linprop_INDUCT;;
	      
let linear_DISTINCT = distinctness "LinProp";;

let linear_INJ = injectivity "LinProp";;


(* ------------------------------------------------------------------------- *)
(* Linear Negation                                                           *)
(* ------------------------------------------------------------------------- *)

(* Conservative definition of linear negation as a function. *)
 
let NEG_CLAUSES = define
  `(NEG LinOne = Bottom) /\
   (NEG Bottom = LinOne) /\
   (NEG LinZero = Top) /\
   (NEG Top = LinZero) /\
   (NEG (A ** B) = (NEG A) % (NEG B)) /\
   (NEG (A % B) = (NEG A) ** (NEG B)) /\
   (NEG (A ++ B ) = (NEG A) && (NEG B)) /\
   (NEG (A && B) = (NEG A) ++ (NEG B)) /\
   (NEG (!! A) = ?? (NEG A)) /\
   (NEG (?? A) = !! (NEG A))`;;


(* Double negation. *)

let NEG_NEG = prove (`!A . NEG (NEG A) = A`, MATCH_MP_TAC linprop_INDUCT THEN simp[NEG_CLAUSES]);;


(* Negation clauses. *)

let [NEG_ONE; NEG_BOTTOM; 
     NEG_ZERO; NEG_TOP;
     NEG_TIMES; NEG_PAR; 
     NEG_PLUS; NEG_WITH; 
     NEG_OFCOURSE ; NEG_WHYNOT] =
  map GEN_ALL (CONJUNCTS NEG_CLAUSES);;


(* Meta-level handling for negation. *)

let is_llneg tm = 
  try fst(dest_const(rator tm)) = "NEG"
  with Failure _ -> false;;

let mk_llneg tm = 
  try ( mk_icomb (`NEG`,tm) ) 
  with Failure s -> failwith ("mk_llneg `" ^ string_of_term tm ^ "` : " ^ s);;

let invert_ll_term tm = 
  try (
    let (comb,args) = strip_comb tm in
    let cll = hd args in
    let cll' = (rhs o concl o (PURE_REWRITE_CONV[NEG_NEG;NEG_CLAUSES]) o (fun x -> mk_comb(`NEG`,x))) cll in
      list_mk_comb (comb,cll'::(tl args))
  ) with Failure _ -> failwith ("invert_ll_term: Invalid term ["^(string_of_term tm)^"]");;

