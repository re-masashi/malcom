(* ast_to_typed_ast.ml *)

open Ast
open Typed_ast
module RawAst = Ast

(* -------------------- Types and Utils (from typechecker.ml, if needed) -------------------- *)

(* Generate fresh type variables *)
let next_type_var = ref 0

let fresh_type_var () =
  let var_name = Printf.sprintf "tv%d" !next_type_var in
  incr next_type_var;
  TVar var_name

(* -------------------- Conversion Functions -------------------- *)

let rec typannot_to_typ (tyann : raw_typannot) : typ =
  match tyann with
  | TAInt -> TInt
  | TABool -> TBool
  | TAStr -> TStr
  | TAUnit -> TUnit
  | TAList ty -> TList (typannot_to_typ ty)
  | TAFun (arg_tyanns, ret_tyann) ->
      TFun (List.map typannot_to_typ arg_tyanns, typannot_to_typ ret_tyann)
  | TAStruct name -> TStruct name
  | TAEnum name -> TEnum name
  | TAVar name -> TVar name
  | TAGeneric (name, type_args) ->
      TGeneric (name, List.map typannot_to_typ type_args)
  | TAConstraint (typ, constr) -> (
      match typannot_to_typ typ with
      | Typed_ast.TVar v -> Typed_ast.TConstrainedVar (v, [ constr ])
      | _ -> failwith "Constraint on non-variable type")

let rec pattern_to_typedpattern (pat : raw_pattern) : typedpattern =
  match pat with
  | RawIntPattern i -> IntPattern i
  | RawVarPattern s -> VarPattern s
  | RawBoolPattern b -> BoolPattern b
  | RawListPattern pats -> ListPattern (List.map pattern_to_typedpattern pats)
  | RawWildcardPattern -> WildcardPattern
  | RawEnumPattern (name, const, pats) ->
      EnumPattern (name, const, List.map pattern_to_typedpattern pats)
  | RawStructPattern fields ->
      StructPattern
        (List.map (fun (n, p) -> (n, pattern_to_typedpattern p)) fields)

let rec expr_to_typedexpr (expr : raw_expr) : expr_t =
  let typed_expr =
    match expr with
    | RawInt i -> Int i
    | RawVar s -> Var (s, fresh_type_var ())
    | RawAdd (e1, e2) -> Add (expr_to_typedexpr e1, expr_to_typedexpr e2)
    | RawSub (e1, e2) -> Sub (expr_to_typedexpr e1, expr_to_typedexpr e2)
    | RawMul (e1, e2) -> Mul (expr_to_typedexpr e1, expr_to_typedexpr e2)
    | RawDiv (e1, e2) -> Div (expr_to_typedexpr e1, expr_to_typedexpr e2)
    | RawLet (s, e1, e2) -> Let (s, expr_to_typedexpr e1, expr_to_typedexpr e2)
    | RawIf (e1, e2, e3) ->
        If (expr_to_typedexpr e1, expr_to_typedexpr e2, expr_to_typedexpr e3)
    | RawBool b -> Bool b
    | RawEqual (e1, e2) -> Equal (expr_to_typedexpr e1, expr_to_typedexpr e2)
    | RawLessThan (e1, e2) ->
        LessThan (expr_to_typedexpr e1, expr_to_typedexpr e2)
    | RawGreaterThan (e1, e2) ->
        GreaterThan (expr_to_typedexpr e1, expr_to_typedexpr e2)
    | RawFun (s, e) -> Fun (s, expr_to_typedexpr e)
    | RawApp (e1, e2) -> App (expr_to_typedexpr e1, expr_to_typedexpr e2)
    | RawUnit -> Unit
    | RawStr s -> Str s
    | RawList exprs -> List (List.map expr_to_typedexpr exprs)
    | RawMatch (e, cases) ->
        Match
          ( expr_to_typedexpr e,
            List.map
              (fun (p, case_expr) ->
                (pattern_to_typedpattern p, expr_to_typedexpr case_expr))
              cases )
    | RawStructAccess (e, s) -> StructAccess (expr_to_typedexpr e, s)
    | RawEnum (enum_name, constructor_name, exprs) ->
        Enum (enum_name, constructor_name, List.map expr_to_typedexpr exprs)
    | RawEnumAccess (e, i) -> EnumAccess (expr_to_typedexpr e, i)
    | RawStruct fields ->
        Struct (List.map (fun (n, e) -> (n, expr_to_typedexpr e)) fields)
    | RawTypeClassInstanceAccess (tc_name, func_name) ->
        TypeClassInstanceAccess (tc_name, func_name)
    | RawBlock exprs -> Block (List.map expr_to_typedexpr exprs)
  in
  { expr = typed_expr; typ = fresh_type_var () }

let toplevel_to_typed_toplevel (top_level : raw_top_level) : typedtop_level =
  match top_level with
  | RawStructDef (name, fields) ->
      StructDef
        (name, List.map (fun (n, tann) -> (n, typannot_to_typ tann)) fields)
  | RawEnumDef (name, constructors) ->
      EnumDef
        ( name,
          List.map
            (fun (ctor_name, tyann_list) ->
              (ctor_name, List.map typannot_to_typ tyann_list))
            constructors )
  | RawFunDef (name, _type_params, params, return_typ_annot, body_expr) ->
      (* 1. Create fresh type variables for each type parameter *)
      (* let fresh_vars = List.map (fun param -> (param, fresh_type_var ())) type_params in *)

      (* 2. Substitute type parameters in raw annotations *)
      let substitute = function
        (* 
        | TAVar name -> 
            (try List.assoc name fresh_vars 
             with Not_found -> Ast.TAVar name)
         | TAGeneric(name, args) ->
            TAGeneric(name, List.map substitute args)
        | TAConstraint(typ, constr) ->
            TAConstraint(substitute typ, constr) *)
        | other -> other
      in

      (* 3. Apply substitution to parameters and return type *)
      let substituted_params =
        List.map (fun (pname, ty) -> (pname, substitute ty)) params
      in
      let substituted_return = substitute return_typ_annot in

      (* 4. Convert substituted raw_typannot to actual typ *)
      let typed_params =
        List.map
          (fun (pname, ty) -> (pname, typannot_to_typ ty))
          substituted_params
      in
      let typed_return = typannot_to_typ substituted_return in

      (* 5. Convert body *)
      let typed_body = expr_to_typedexpr body_expr in

      FunDef (name, typed_params, typed_return, typed_body)
  | RawTypeClassDef (name, function_signatures) ->
      TypeClassDef
        ( name,
          List.map
            (fun (func_name, typannot) -> (func_name, typannot_to_typ typannot))
            function_signatures )
  | RawInstanceDef (typeclass_name, type_annot, function_impls) ->
      InstanceDef
        ( typeclass_name,
          typannot_to_typ type_annot,
          List.map
            (fun (func_name, expr) -> (func_name, expr_to_typedexpr expr))
            function_impls )

let convert_program (raw_tops : raw_top_level list) : Typed_ast.program =
  let structs = ref [] in
  let enums = ref [] in
  let top_levels = ref [] in

  List.iter
    (fun raw_top ->
      match raw_top with
      | RawStructDef (name, fields) ->
          let typed_fields =
            List.map (fun (n, t) -> (n, typannot_to_typ t)) fields
          in
          structs := (name, typed_fields) :: !structs
      | RawEnumDef (name, ctors) ->
          let typed_ctors =
            List.map (fun (n, ts) -> (n, List.map typannot_to_typ ts)) ctors
          in
          enums := (name, typed_ctors) :: !enums
      | other -> top_levels := toplevel_to_typed_toplevel other :: !top_levels)
    raw_tops;

  { structs = !structs; enums = !enums; top_levels = List.rev !top_levels }
