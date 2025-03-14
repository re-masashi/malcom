
(* Test 1: Nested generics *)
let test_substitution_generic () =
  Hashtbl.add substitution_env "'a" TInt;
  let original = TGeneric("List", [TGeneric("Option", [TVar "'a"])]) in
  let result = replace_typevars_typ original in
  assert(result = TGeneric("List", [TGeneric("Option", [TInt])]))

(* Test 2: Constrained variable substitution *)
let test_substitution_constrained () =
  Hashtbl.add substitution_env "'b" TInt;
  let original = TConstrainedVar("'b", ["Eq"]) in
  let result = replace_typevars_typ original in
  assert(result = TInt) (* Should trigger Eq constraint check later *)