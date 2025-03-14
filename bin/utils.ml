(* utils.ml *)

open Ast
open Typed_ast

(* -------------------- String Conversion Functions for AST -------------------- *)

let rec string_of_typ typ =
  match typ with
  | TInt -> "Int"
  | TBool -> "Bool"
  | TStr -> "Str"
  | TUnit -> "Unit"
  | TList ty -> Printf.sprintf "List<%s>" (string_of_typ ty)
  | TFun (arg_types, return_type) ->
      let arg_types_str =
        String.concat ", " (List.map string_of_typ arg_types)
      in
      Printf.sprintf "(%s) => %s" arg_types_str (string_of_typ return_type)
  | TStruct name -> Printf.sprintf "Struct<%s>" name
  | TEnum name -> Printf.sprintf "Enum<%s>" name
  | TVar name -> Printf.sprintf "'%s" name
  | TGeneric (name, type_args) ->
      Printf.sprintf "%s<%s>" name
        (String.concat ", " (List.map string_of_typ type_args))
  | TConstrainedVar (name, constraints) ->
      Printf.sprintf "'%s with [%s]" name (String.concat ", " constraints)
  | TTypeClass name -> Printf.sprintf "TypeClass<%s>" name

let rec string_of_expr expr =
  let rec to_string e =
    match e with
    | RawInt i -> string_of_int i
    | RawBool b -> string_of_bool b
    | RawStr s -> "\"" ^ s ^ "\""
    | RawUnit -> "()"
    | RawVar s -> s
    | RawAdd (e1, e2) -> "(" ^ to_string e1 ^ " + " ^ to_string e2 ^ ")"
    | RawSub (e1, e2) -> "(" ^ to_string e1 ^ " - " ^ to_string e2 ^ ")"
    | RawMul (e1, e2) -> "(" ^ to_string e1 ^ " * " ^ to_string e2 ^ ")"
    | RawDiv (e1, e2) -> "(" ^ to_string e1 ^ " / " ^ to_string e2 ^ ")"
    | RawEqual (e1, e2) -> "(" ^ to_string e1 ^ " == " ^ to_string e2 ^ ")"
    | RawLessThan (e1, e2) -> "(" ^ to_string e1 ^ " < " ^ to_string e2 ^ ")"
    | RawGreaterThan (e1, e2) -> "(" ^ to_string e1 ^ " > " ^ to_string e2 ^ ")"
    | RawLet (var, expr, body) ->
        Printf.sprintf "let %s = %s in %s" var (to_string expr) (to_string body)
    | RawIf (cond, then_expr, else_expr) ->
        Printf.sprintf "if %s then %s else %s" (to_string cond)
          (to_string then_expr) (to_string else_expr)
    | RawFun (param, body) ->
        Printf.sprintf "fun %s -> %s" param (to_string body)
    | RawApp (fun_expr, arg_expr) ->
        Printf.sprintf "(%s) (%s)" (to_string fun_expr) (to_string arg_expr)
    | RawList exprs -> "[" ^ String.concat "; " (List.map to_string exprs) ^ "]"
    | RawMatch (expr, cases) ->
        let case_to_string (pat, case_expr) =
          Printf.sprintf "| %s -> %s" (string_of_pattern pat)
            (to_string case_expr)
        in
        Printf.sprintf "match %s with\n%s\nend" (to_string expr)
          (String.concat "\n" (List.map case_to_string cases))
    | RawStructAccess (expr, field) ->
        Printf.sprintf "%s.%s" (to_string expr) field
    | RawEnum (enum_name, constructor_name, exprs) ->
        Printf.sprintf "%s.%s(%s)" enum_name constructor_name
          (String.concat ", " (List.map to_string exprs))
    | RawEnumAccess (expr, index) ->
        Printf.sprintf "%s.(%d)" (to_string expr) index
    | RawStruct fields ->
        let field_to_string (name, expr) =
          Printf.sprintf "%s = %s" name (to_string expr)
        in
        Printf.sprintf "{ %s }"
          (String.concat "; " (List.map field_to_string fields))
    | RawTypeClassInstanceAccess (tc_name, func_name) ->
        Printf.sprintf "%s.%s" tc_name func_name
    | RawBlock _exprs -> Printf.sprintf "do \n  \n end"
  in
  to_string expr

and string_of_pattern pattern =
  let rec to_string pat =
    match pat with
    | RawIntPattern i -> string_of_int i
    | RawBoolPattern b -> string_of_bool b
    | RawVarPattern s -> s
    | RawListPattern pats ->
        "[" ^ String.concat "; " (List.map to_string pats) ^ "]"
    | RawWildcardPattern -> "_"
    | RawEnumPattern (name, const, pats) ->
        Printf.sprintf "%s::%s(%s)" name const
          (String.concat ", " (List.map to_string pats))
    | RawStructPattern fields ->
        let field_to_string (name, pat) =
          Printf.sprintf "%s = %s" name (to_string pat)
        in
        Printf.sprintf "{ %s }"
          (String.concat "; " (List.map field_to_string fields))
  in
  to_string pattern

let rec string_of_top_level top_level =
  match top_level with
  | RawStructDef (name, fields) ->
      let field_to_string (name, typannot) =
        Printf.sprintf "%s : %s" name (string_of_typannot typannot)
      in
      Printf.sprintf "struct %s {\n  %s\n}" name
        (String.concat ";\n  " (List.map field_to_string fields))
  | RawEnumDef (name, constructors) ->
      let constructor_to_string (ctor_name, tyann_list) =
        Printf.sprintf "| %s of %s" ctor_name
          (String.concat " * " (List.map string_of_typannot tyann_list))
      in
      Printf.sprintf "enum %s =\n%s" name
        (String.concat "\n" (List.map constructor_to_string constructors))
  | RawFunDef (name, type_params, params, return_typ_annot, body_expr) ->
      let type_params_str =
        match type_params with
        | [] -> ""
        | params -> Printf.sprintf "<%s>" (String.concat ", " params)
      in
      let param_to_string (p_name, typannot) =
        Printf.sprintf "%s : %s" p_name (string_of_typannot typannot)
      in
      Printf.sprintf "fun%s %s (%s) : %s = %s" type_params_str name
        (String.concat ", " (List.map param_to_string params))
        (string_of_typannot return_typ_annot)
        (string_of_expr body_expr)
  | RawTypeClassDef (name, function_signatures) ->
      let func_sig_to_string (func_name, typannot) =
        Printf.sprintf "  %s : %s;" func_name (string_of_typannot typannot)
      in
      Printf.sprintf "typeclass %s {\n%s\n}" name
        (String.concat "\n" (List.map func_sig_to_string function_signatures))
  | RawInstanceDef (typeclass_name, type_annot, function_impls) ->
      let func_impl_to_string (func_name, expr) =
        Printf.sprintf "  %s = %s;" func_name (string_of_expr expr)
      in
      Printf.sprintf "instance %s %s {\n%s\n}" typeclass_name
        (string_of_typannot type_annot)
        (String.concat "\n" (List.map func_impl_to_string function_impls))

and string_of_typannot typannot =
  match typannot with
  | TAInt -> "Int"
  | TABool -> "Bool"
  | TAStr -> "Str"
  | TAUnit -> "Unit"
  | TAList ty -> Printf.sprintf "List<%s>" (string_of_typannot ty)
  | TAFun (arg_tyanns, ret_tyann) ->
      let arg_types_str =
        String.concat ", " (List.map string_of_typannot arg_tyanns)
      in
      Printf.sprintf "(%s) => %s" arg_types_str (string_of_typannot ret_tyann)
  | TAStruct name -> Printf.sprintf "Struct<%s>" name
  | TAEnum name -> Printf.sprintf "Enum<%s>" name
  | TAVar name -> Printf.sprintf "'%s" name
  | TAGeneric (name, type_args) ->
      Printf.sprintf "%s<%s>" name
        (String.concat ", " (List.map string_of_typannot type_args))
  | TAConstraint (tyann, tc_name) ->
      Printf.sprintf "%s : %s" (string_of_typannot tyann) tc_name

(* -------------------- String Conversion Functions for Typed AST -------------------- *)

let rec string_of_typedexpr expr_t =
  let rec to_string te =
    match te.expr with
    | Int i -> string_of_int i
    | Bool b -> string_of_bool b
    | Str s -> "\"" ^ s ^ "\""
    | Unit -> "()"
    | Var (s, typ) -> Printf.sprintf "%s : %s" s (string_of_typ typ)
    | Add (e1, e2) -> "(" ^ to_string e1 ^ " + " ^ to_string e2 ^ ")"
    | Sub (e1, e2) -> "(" ^ to_string e1 ^ " - " ^ to_string e2 ^ ")"
    | Mul (e1, e2) -> "(" ^ to_string e1 ^ " * " ^ to_string e2 ^ ")"
    | Div (e1, e2) -> "(" ^ to_string e1 ^ " / " ^ to_string e2 ^ ")"
    | Equal (e1, e2) -> "(" ^ to_string e1 ^ " == " ^ to_string e2 ^ ")"
    | LessThan (e1, e2) -> "(" ^ to_string e1 ^ " < " ^ to_string e2 ^ ")"
    | GreaterThan (e1, e2) -> "(" ^ to_string e1 ^ " > " ^ to_string e2 ^ ")"
    | Let (var, expr, body) ->
        Printf.sprintf "let %s = %s in %s" var (to_string expr) (to_string body)
    | If (cond, then_expr, else_expr) ->
        Printf.sprintf "if %s then %s else %s" (to_string cond)
          (to_string then_expr) (to_string else_expr)
    | Fun (param, body) -> Printf.sprintf "fun %s -> %s" param (to_string body)
    | App (fun_expr, arg_expr) ->
        Printf.sprintf "(%s) (%s)" (to_string fun_expr) (to_string arg_expr)
    | List exprs -> "[" ^ String.concat "; " (List.map to_string exprs) ^ "]"
    | Match (expr, cases) ->
        let case_to_string (pat, case_expr) =
          Printf.sprintf "| %s -> %s"
            (string_of_typedpattern pat)
            (to_string case_expr)
        in
        Printf.sprintf "match %s with\n%s\nend" (to_string expr)
          (String.concat "\n" (List.map case_to_string cases))
    | StructAccess (expr, field) ->
        Printf.sprintf "%s.%s" (to_string expr) field
    | Enum (enum_name, constructor_name, exprs) ->
        Printf.sprintf "%s.%s(%s)" enum_name constructor_name
          (String.concat ", " (List.map to_string exprs))
    | EnumAccess (expr, index) ->
        Printf.sprintf "%s.(%d)" (to_string expr) index
    | Struct fields ->
        let field_to_string (name, expr) =
          Printf.sprintf "%s = %s" name (to_string expr)
        in
        Printf.sprintf "{ %s }"
          (String.concat "; " (List.map field_to_string fields))
    | TypeClassInstanceAccess (tc_name, func_name) ->
        Printf.sprintf "%s.%s" tc_name func_name
    | Block _ -> Printf.sprintf "do end"
  in
  to_string expr_t

and string_of_typedpattern typed_pattern =
  let rec to_string tp =
    match tp with
    | IntPattern i -> string_of_int i
    | BoolPattern b -> string_of_bool b
    | VarPattern s -> s
    | ListPattern pats ->
        "[" ^ String.concat "; " (List.map to_string pats) ^ "]"
    | WildcardPattern -> "_"
    | EnumPattern (name, const, pats) ->
        Printf.sprintf "%s::%s(%s)" name const
          (String.concat ", " (List.map to_string pats))
    | StructPattern fields ->
        let field_to_string (name, pat) =
          Printf.sprintf "%s = %s" name (to_string pat)
        in
        Printf.sprintf "{ %s }"
          (String.concat "; " (List.map field_to_string fields))
  in
  to_string typed_pattern

let string_of_typedtop_level typed_top_level =
  match typed_top_level with
  | StructDef (name, fields) ->
      let field_to_string (name, typ) =
        Printf.sprintf "%s : %s" name (string_of_typ typ)
      in
      Printf.sprintf "struct %s {\n  %s\n}" name
        (String.concat ";\n  " (List.map field_to_string fields))
  | EnumDef (name, constructors) ->
      let constructor_to_string (ctor_name, typ_list) =
        Printf.sprintf "| %s of %s" ctor_name
          (String.concat " * " (List.map string_of_typ typ_list))
      in
      Printf.sprintf "enum %s =\n%s" name
        (String.concat "\n" (List.map constructor_to_string constructors))
  | FunDef (name, params, return_typ, body_expr) ->
      let param_to_string (p_name, typ) =
        Printf.sprintf "%s : %s" p_name (string_of_typ typ)
      in
      Printf.sprintf "fun %s (%s) : %s = %s" name
        (String.concat ", " (List.map param_to_string params))
        (string_of_typ return_typ)
        (string_of_typedexpr body_expr)
  | TypeClassDef (name, function_signatures) ->
      let func_sig_to_string (func_name, typ) =
        Printf.sprintf "  %s : %s;" func_name (string_of_typ typ)
      in
      Printf.sprintf "typeclass %s {\n%s\n}" name
        (String.concat "\n" (List.map func_sig_to_string function_signatures))
  | InstanceDef (typeclass_name, instance_type, function_impls) ->
      let func_impl_to_string (func_name, expr) =
        Printf.sprintf "  %s = %s;" func_name (string_of_typedexpr expr)
      in
      Printf.sprintf "instance %s %s {\n%s\n}" typeclass_name
        (string_of_typ instance_type)
        (String.concat "\n" (List.map func_impl_to_string function_impls))

and string_of_typ typ =
  match typ with
  | TInt -> "Int"
  | TBool -> "Bool"
  | TStr -> "Str"
  | TUnit -> "Unit"
  | TList ty -> Printf.sprintf "List<%s>" (string_of_typ ty)
  | TFun (arg_types, return_type) ->
      let arg_types_str =
        String.concat ", " (List.map string_of_typ arg_types)
      in
      Printf.sprintf "(%s) => %s" arg_types_str (string_of_typ return_type)
  | TStruct name -> Printf.sprintf "Struct<%s>" name
  | TEnum name -> Printf.sprintf "Enum<%s>" name
  | TVar name -> Printf.sprintf "'%s" name
  | TGeneric (name, type_args) ->
      Printf.sprintf "%s<%s>" name
        (String.concat ", " (List.map string_of_typ type_args))
  | TConstrainedVar (name, constraints) ->
      Printf.sprintf "'%s with [%s]" name (String.concat ", " constraints)
  | TTypeClass name -> Printf.sprintf "TypeClass<%s>" name

(* -------------------- Printing Functions for Top-Levels (Structs and Enums) -------------------- *)

let print_struct_def top_level =
  match top_level with
  | RawStructDef _ -> print_endline (string_of_top_level top_level)
  | _ -> print_endline "Not a Struct Definition"

let print_enum_def top_level =
  match top_level with
  | RawEnumDef _ -> print_endline (string_of_top_level top_level)
  | _ -> print_endline "Not an Enum Definition"

let print_top_level top_level = print_endline (string_of_top_level top_level)

let print_typed_top_level typed_top_level =
  print_endline (string_of_typedtop_level typed_top_level)

let print_expr expr = print_endline (string_of_expr expr)
let print_typedexpr expr_t = print_endline (string_of_typedexpr expr_t)
