(* typechecker.ml *)

open Ast
open Typed_ast

(* open Location *)
open Utils

(* open Hashtbl *)
(* open Ast_to_typed_ast *)

(* -------------------- Types and Utils -------------------- *)

(* Type environment: mapping from variable name to type *)
module Env = Map.Make (String)

type type_env = typ Env.t

(* Typeclass environment: mapping from typeclass name to function signatures *)
let type_class_env : (string, (string * raw_typannot) list) Hashtbl.t =
  Hashtbl.create 10

(* Instance environment: mapping from (typeclass name, type name) to instance implementations *)
let instance_env : (string * string, (string * expr_t) list) Hashtbl.t =
  Hashtbl.create 10

(* Substitution environment: mapping from type variable names to types *)
let substitution_env : (string, typ) Hashtbl.t = Hashtbl.create 10

(* let struct_defs : (string, (string * typ) list) Hashtbl.t = Hashtbl.create 10
let enum_defs : (string, (string * typ list) list) Hashtbl.t = Hashtbl.create 10
 *)
(* Generate fresh type variables *)
let next_type_var = ref 0

let fresh_type_var () =
  let var_name = Printf.sprintf "tv%d" !next_type_var in
  incr next_type_var;
  TVar var_name

exception TypeError of string * Location.t option

let error msg loc = raise (TypeError (msg, loc))
let dummy_loc = Location.dummy

(* Helper function to get location from expr_t *)
let get_expr_loc _expr_t = dummy_loc
(* Replace with actual location tracking if available in Ast - using dummy for now *)

(* -------------------- Unification -------------------- *)

let rec occurs_check var_name typ =
  match typ with
  | TVar name' -> name' = var_name
  | TList typ' -> occurs_check var_name typ'
  | TFun (arg_types, return_type) ->
      List.exists (occurs_check var_name) arg_types
      || occurs_check var_name return_type
  | TGeneric (_name, type_args) -> List.exists (occurs_check var_name) type_args
  | TConstrainedVar (name', _constraints) -> name' = var_name
  | TStruct _ | TEnum _ | TInt | TBool | TStr | TUnit | TTypeClass _ -> false

(* Assuming TStruct and TEnum names are unique and don't need occurs check *)

let rec unify typ1 typ2 =
  if typ1 == typ2 then () (* Physical equality optimization *)
  else
    match (typ1, typ2) with
    | TVar var_name, typ ->
        if occurs_check var_name typ then
          error
            ("Occurs check failed: " ^ var_name ^ " in " ^ string_of_typ typ)
            (Some dummy_loc)
        else if typ <> TVar var_name then (
          Hashtbl.replace substitution_env var_name typ;
          (* Store substitution *)
          ())
    | typ, TVar var_name -> unify (TVar var_name) typ (* Commutativity *)
    | TFun (arg_types1, return_type1), TFun (arg_types2, return_type2) ->
        if List.length arg_types1 <> List.length arg_types2 then
          error "Function argument count mismatch" (Some dummy_loc);
        List.iter2 unify arg_types1 arg_types2;
        unify return_type1 return_type2
    | TList typ1', TList typ2' -> unify typ1' typ2'
    | TGeneric (name1, args1), TGeneric (name2, args2)
      when name1 = name2 && List.length args1 = List.length args2 ->
        List.iter2 unify args1 args2
    | TStruct name1, TStruct name2 when name1 = name2 -> ()
    | TEnum name1, TEnum name2 when name1 = name2 -> ()
    | TInt, TInt -> ()
    | TBool, TBool -> ()
    | TStr, TStr -> ()
    | TUnit, TUnit -> ()
    | TConstrainedVar (v, constraints), concrete ->
        List.iter (fun c -> check_constraint v c concrete) constraints
    | concrete, TConstrainedVar (v, constraints) ->
        List.iter (fun c -> check_constraint v c concrete) constraints
    | _ ->
        error
          ("Type mismatch: " ^ string_of_typ typ1 ^ " and " ^ string_of_typ typ2)
          (Some dummy_loc)

and check_constraint _var_name constraint_name concrete =
  let type_str = string_of_typ concrete in
  match Hashtbl.find_opt instance_env (constraint_name, type_str) with
  | Some _ -> ()
  | None ->
      error
        (Printf.sprintf "Type %s doesn't satisfy %s constraint" type_str
           constraint_name)
        None

(* -------------------- Type Variable Substitution -------------------- *)

let rec replace_typevars_typ typ : typ =
  match typ with
  | TVar name' -> (
      try
        let actual_type = Hashtbl.find substitution_env name' in
        let replaced_actual_type = replace_typevars_typ actual_type in
        (* Recursively replace in substituted type *)
        replaced_actual_type
      with Not_found ->
        (* If no concrete type found, it remains a type variable (could be polymorphic) *)
        typ)
  | TList typ' -> TList (replace_typevars_typ typ')
  | TFun (arg_types, return_type) ->
      TFun
        ( List.map replace_typevars_typ arg_types,
          replace_typevars_typ return_type )
  | TGeneric (name, type_args) ->
      TGeneric (name, List.map replace_typevars_typ type_args)
  | TConstrainedVar (name', constraints) -> (
      (* Substitute constrained variables *)
      try
        let substituted = Hashtbl.find substitution_env name' in
        replace_typevars_typ substituted
      with Not_found -> TConstrainedVar (name', constraints))
  | TStruct name -> TStruct name
  | TEnum name -> TEnum name
  | TInt -> TInt
  | TBool -> TBool
  | TStr -> TStr
  | TUnit -> TUnit
  | TTypeClass name -> TTypeClass name
(* | TVar _ -> typ (* PolyTypes should remain as they are *) *)

let rec replace_typevars_expr (expr_t : expr_t) : expr_t =
  let replaced_typ = replace_typevars_typ expr_t.typ in
  match expr_t.expr with
  | Var (name, _typ) -> { expr = Var (name, replaced_typ); typ = replaced_typ }
  | Int _ | Bool _ | Str _ | Unit | TypeClassInstanceAccess _ ->
      { expr = expr_t.expr; typ = replaced_typ } (* No sub-expressions *)
  | Add (e1, e2) ->
      {
        expr = Add (replace_typevars_expr e1, replace_typevars_expr e2);
        typ = replaced_typ;
      }
  | Sub (e1, e2) ->
      {
        expr = Sub (replace_typevars_expr e1, replace_typevars_expr e2);
        typ = replaced_typ;
      }
  | Mul (e1, e2) ->
      {
        expr = Mul (replace_typevars_expr e1, replace_typevars_expr e2);
        typ = replaced_typ;
      }
  | Div (e1, e2) ->
      {
        expr = Div (replace_typevars_expr e1, replace_typevars_expr e2);
        typ = replaced_typ;
      }
  | Equal (e1, e2) ->
      {
        expr = Equal (replace_typevars_expr e1, replace_typevars_expr e2);
        typ = replaced_typ;
      }
  | LessThan (e1, e2) ->
      {
        expr = LessThan (replace_typevars_expr e1, replace_typevars_expr e2);
        typ = replaced_typ;
      }
  | GreaterThan (e1, e2) ->
      {
        expr = GreaterThan (replace_typevars_expr e1, replace_typevars_expr e2);
        typ = replaced_typ;
      }
  | Let (name, val_expr, body_expr) ->
      {
        expr =
          Let
            ( name,
              replace_typevars_expr val_expr,
              replace_typevars_expr body_expr );
        typ = replaced_typ;
      }
  | If (cond_expr, then_expr, else_expr) ->
      {
        expr =
          If
            ( replace_typevars_expr cond_expr,
              replace_typevars_expr then_expr,
              replace_typevars_expr else_expr );
        typ = replaced_typ;
      }
  | Fun (param_name, body_expr) ->
      {
        expr = Fun (param_name, replace_typevars_expr body_expr);
        typ = replaced_typ;
      }
  | App (fun_expr, arg_expr) ->
      {
        expr =
          App (replace_typevars_expr fun_expr, replace_typevars_expr arg_expr);
        typ = replaced_typ;
      }
  | List expr_list ->
      {
        expr = List (List.map replace_typevars_expr expr_list);
        typ = replaced_typ;
      }
  | Match (match_expr, cases) ->
      let replaced_cases =
        List.map
          (fun (pattern, case_expr) ->
            (pattern, replace_typevars_expr case_expr))
          cases
      in
      {
        expr = Match (replace_typevars_expr match_expr, replaced_cases);
        typ = replaced_typ;
      }
  | StructAccess (struct_expr, field_name) ->
      {
        expr = StructAccess (replace_typevars_expr struct_expr, field_name);
        typ = replaced_typ;
      }
  | Enum (enum_name, constructor_name, arg_exprs) ->
      {
        expr =
          Enum
            ( enum_name,
              constructor_name,
              List.map replace_typevars_expr arg_exprs );
        typ = replaced_typ;
      }
  | EnumAccess (enum_expr, index) ->
      {
        expr = EnumAccess (replace_typevars_expr enum_expr, index);
        typ = replaced_typ;
      }
  | Struct fields ->
      let replaced_fields =
        List.map
          (fun (field_name, field_expr) ->
            (field_name, replace_typevars_expr field_expr))
          fields
      in
      { expr = Struct replaced_fields; typ = replaced_typ }
  | Block expr_list ->
      (* Handle Block case *)
      let replaced_expr_list = List.map replace_typevars_expr expr_list in
      let block_type =
        match List.rev replaced_expr_list with
        | last_expr :: _ ->
            last_expr.typ (* Type of block is type of last expression *)
        | [] -> TUnit (* Empty block has Unit type *)
      in
      { expr = Block replaced_expr_list; typ = block_type }

let rec replace_typevars_pattern (pattern : typedpattern) : typedpattern =
  match pattern with
  | IntPattern _ | BoolPattern _ | VarPattern _ | WildcardPattern ->
      pattern
      (* No types to replace directly in these patterns, types are in the expressions using these bindings *)
  | ListPattern patterns ->
      ListPattern (List.map (fun p -> replace_typevars_pattern p) patterns)
  | EnumPattern (enum_name, const, patterns) ->
      EnumPattern (enum_name, const, List.map replace_typevars_pattern patterns)
  | StructPattern fields ->
      StructPattern
        (List.map
           (fun (field_name, field_pattern) ->
             (field_name, replace_typevars_pattern field_pattern))
           fields)

let replace_typevars_top_level (top_level : typedtop_level) : typedtop_level =
  match top_level with
  | FunDef (name, params, return_typ, body_expr) ->
      let replaced_params =
        List.map
          (fun (p_name, p_type) -> (p_name, replace_typevars_typ p_type))
          params
      in
      let replaced_return_typ = replace_typevars_typ return_typ in
      let replaced_body_expr = replace_typevars_expr body_expr in
      FunDef (name, replaced_params, replaced_return_typ, replaced_body_expr)
  | StructDef (name, fields) ->
      let replaced_fields =
        List.map
          (fun (field_name, field_type) ->
            (field_name, replace_typevars_typ field_type))
          fields
      in
      StructDef (name, replaced_fields)
  | EnumDef (name, constructors) ->
      let replaced_constructors =
        List.map
          (fun (ctor_name, arg_types) ->
            (ctor_name, List.map replace_typevars_typ arg_types))
          constructors
      in
      EnumDef (name, replaced_constructors)
  | TypeClassDef (name, function_signatures) ->
      let replaced_function_signatures =
        List.map
          (fun (func_name, typ) -> (func_name, replace_typevars_typ typ))
          function_signatures
      in
      TypeClassDef (name, replaced_function_signatures)
  | InstanceDef (typeclass_name, instance_type, function_impls) ->
      let replaced_instance_type = replace_typevars_typ instance_type in
      let replaced_function_impls =
        List.map
          (fun (func_name, expr_t) -> (func_name, replace_typevars_expr expr_t))
          function_impls
      in
      InstanceDef
        (typeclass_name, replaced_instance_type, replaced_function_impls)

let replace_typevars_program (typed_top_levels : typedtop_level list) :
    typedtop_level list =
  List.map replace_typevars_top_level typed_top_levels

(* -------------------- Type Checking Expressions and Constructing Typed AST -------------------- *)

let rec typecheck_expr env (raw_expr_t : raw_expr) : expr_t * typ =
  (* Return typed expr and type *)
  let loc = get_expr_loc raw_expr_t in
  match raw_expr_t with
  | RawInt i ->
      let typ = TInt in
      ({ expr = Int i; typ }, typ)
      (* Construct Typed AST node and return type *)
  | RawBool b ->
      let typ = TBool in
      ({ expr = Bool b; typ }, typ)
  | RawStr s ->
      let typ = TStr in
      ({ expr = Str s; typ }, typ)
  | RawUnit ->
      let typ = TUnit in
      ({ expr = Unit; typ }, typ)
  | RawVar s -> (
      try
        let var_type = Env.find s env in
        ({ expr = Var (s, var_type); typ = var_type }, var_type)
      with Not_found -> error ("Unbound variable: " ^ s) (Some dummy_loc))
  | RawAdd (e1, e2) ->
      let typed_e1, typ1 = typecheck_expr env e1 in
      let typed_e2, typ2 = typecheck_expr env e2 in
      unify typ1 TInt;
      unify typ2 TInt;
      let typ = TInt in
      ({ expr = Add (typed_e1, typed_e2); typ }, typ)
  | RawSub (e1, e2) ->
      let typed_e1, typ1 = typecheck_expr env e1 in
      let typed_e2, typ2 = typecheck_expr env e2 in
      unify typ1 TInt;
      unify typ2 TInt;
      let typ = TInt in
      ({ expr = Sub (typed_e1, typed_e2); typ }, typ)
  | RawMul (e1, e2) ->
      let typed_e1, typ1 = typecheck_expr env e1 in
      let typed_e2, typ2 = typecheck_expr env e2 in
      unify typ1 TInt;
      unify typ2 TInt;
      let typ = TInt in
      ({ expr = Mul (typed_e1, typed_e2); typ }, typ)
  | RawDiv (e1, e2) ->
      let typed_e1, typ1 = typecheck_expr env e1 in
      let typed_e2, typ2 = typecheck_expr env e2 in
      unify typ1 TInt;
      unify typ2 TInt;
      let typ = TInt in
      ({ expr = Div (typed_e1, typed_e2); typ }, typ)
  | RawEqual (e1, e2) | RawLessThan (e1, e2) | RawGreaterThan (e1, e2) ->
      let typed_e1, typ1 = typecheck_expr env e1 in
      let typed_e2, typ2 = typecheck_expr env e2 in
      unify typ1 typ2;
      (* Both operands must have the same type *)
      let typ = TBool in
      ({ expr = Equal (typed_e1, typed_e2); typ }, typ)
      (* Assuming Equal, LessThan, GreaterThan all return Bool *)
  | RawLet (name, value_expr, body_expr) ->
      let typed_value_expr, value_type = typecheck_expr env value_expr in
      let env' = Env.add name value_type env in
      let typed_body_expr, body_type = typecheck_expr env' body_expr in
      let typ = body_type in
      (* Let expression returns the type of the body *)
      ({ expr = Let (name, typed_value_expr, typed_body_expr); typ }, typ)
  | RawIf (cond_expr, then_expr, else_expr) ->
      let typed_cond_expr, cond_type = typecheck_expr env cond_expr in
      unify cond_type TBool;
      let typed_then_expr, then_type = typecheck_expr env then_expr in
      let typed_else_expr, else_type = typecheck_expr env else_expr in
      unify then_type else_type;
      (* Both branches must have the same type *)
      let typ = then_type in
      (* If expression returns the type of the then/else branch *)
      ( { expr = If (typed_cond_expr, typed_then_expr, typed_else_expr); typ },
        typ )
  | RawFun (param_name, body_expr) ->
      let param_type = fresh_type_var () in
      (* Infer param type *)
      let env' = Env.add param_name param_type env in
      let typed_body_expr, return_type = typecheck_expr env' body_expr in
      let typ = TFun ([ param_type ], return_type) in
      ({ expr = Fun (param_name, typed_body_expr); typ }, typ)
  | RawApp (fun_expr, arg_expr) -> (
      let typed_fun_expr, fun_type = typecheck_expr env fun_expr in
      let typed_arg_expr, arg_type = typecheck_expr env arg_expr in
      let return_type = fresh_type_var () in
      (* Infer return type *)

      match fun_type with
      | TFun (expected_arg_types, expected_return_type) ->
          if List.length expected_arg_types <> 1 then
            (* Simple example - functions of one arg *)
            error "Function application: incorrect number of arguments" None;
          let expected_arg_type = List.hd expected_arg_types in
          unify expected_arg_type arg_type;
          (* Unify argument type with expected type *)
          unify return_type expected_return_type;
          (* Unify return type *)
          let typ = return_type in
          ({ expr = App (typed_fun_expr, typed_arg_expr); typ }, typ)
      | TConstrainedVar (_var_name, typeclass_names) ->
          (* Example: Typeclass constrained function - basic constraint check *)
          (* Simple constraint check: Is there ANY instance defined for the typeclasses for arg_type? *)
          List.iter
            (fun tc_name ->
              try
                ignore
                  (Hashtbl.find instance_env (tc_name, string_of_typ arg_type))
              with Not_found ->
                error
                  ("Typeclass constraint not satisfied: Type "
                 ^ string_of_typ arg_type ^ " does not implement typeclass "
                 ^ tc_name)
                  (Some loc))
            typeclass_names;

          unify fun_type (TFun ([ arg_type ], return_type));
          (* For simplicity, still unify with TFun, but constraints are now checked *)
          let typ = return_type in
          ({ expr = App (typed_fun_expr, typed_arg_expr); typ }, typ)
      | _ ->
          error
            ("Application of non-function type: " ^ string_of_typ fun_type)
            None)
  | RawList expr_list -> (
      match expr_list with
      | [] ->
          let element_type = fresh_type_var () in
          let typ = TList element_type in
          ({ expr = List []; typ }, typ)
          (* Empty list can be list of any type *)
      | first_expr :: rest_exprs ->
          let typed_first_expr, first_type = typecheck_expr env first_expr in
          let typed_rest_exprs_and_types =
            List.map (fun expr -> typecheck_expr env expr) rest_exprs
          in
          List.iter
            (fun (_, typ) -> unify first_type typ)
            typed_rest_exprs_and_types;
          let typed_expr_list =
            typed_first_expr :: List.map fst typed_rest_exprs_and_types
          in
          let typ = TList first_type in
          ({ expr = List typed_expr_list; typ }, typ))
  | RawMatch (match_expr, cases) ->
      let typed_match_expr, match_type = typecheck_expr env match_expr in
      let result_type = fresh_type_var () in
      (* Result type of the match expression *)
      let typed_cases =
        List.map
          (fun (pattern, case_expr) ->
            let pattern_env, typed_pattern =
              typecheck_pattern env pattern match_type
            in
            (* Extend env based on pattern *)
            let typed_case_expr, case_type =
              typecheck_expr pattern_env case_expr
            in
            unify result_type case_type;
            (* All cases must have the same result type *)
            (typed_pattern, typed_case_expr))
          cases
      in
      let typ = result_type in
      ({ expr = Match (typed_match_expr, typed_cases); typ }, typ)
  | RawStructAccess (struct_expr, field_name) -> (
      let typed_struct_expr, struct_type = typecheck_expr env struct_expr in
      match struct_type with
      | TStruct struct_name -> (
          match Hashtbl.find_opt struct_defs struct_name with
          | Some fields_def -> (
              match List.assoc_opt field_name fields_def with
              | Some field_type ->
                  let typ = field_type in
                  ( { expr = StructAccess (typed_struct_expr, field_name); typ },
                    typ )
              | None ->
                  error
                    ("Field '" ^ field_name ^ "' not found in struct '"
                   ^ struct_name ^ "'")
                    (Some loc))
          | None -> error ("Struct '" ^ struct_name ^ "' not found") (Some loc))
      | _ -> error "Struct access on non-struct type" (Some loc))
  | RawEnum (enum_name, constructor_name, arg_exprs) ->
      let typed_arg_exprs_and_types =
        List.map (fun expr -> typecheck_expr env expr) arg_exprs
      in
      let typed_arg_exprs = List.map fst typed_arg_exprs_and_types in
      (* Need to lookup enum definition and constructor signature *)
      (* Placeholder - In real implementation, we'd need to access EnumDef info and check arg types against constructor *)
      let typ = TEnum enum_name in
      (* For now, assume Enum construction is always valid and return enum type *)
      ({ expr = Enum (enum_name, constructor_name, typed_arg_exprs); typ }, typ)  
  | RawEnumAccess (enum_expr, index) -> (
      let typed_enum_expr, enum_type = typecheck_expr env enum_expr in
      match enum_type with
      | TEnum _enum_name ->
          (* Need to lookup enum definition and constructor types at index *)
          (* Placeholder - In real implementation, we'd need to access EnumDef info *)
          let enum_element_type = fresh_type_var () in
          (* For now, assume enum access is always valid and infer type *)
          let typ = enum_element_type in
          ({ expr = EnumAccess (typed_enum_expr, index); typ }, typ)
      | _ -> error "Enum access on non-enum type" (Some dummy_loc))
  | RawStruct fields ->
      let typed_fields_and_types =
        List.map
          (fun (field_name, field_expr) ->
            let typed_field_expr, field_type = typecheck_expr env field_expr in
            ((field_name, typed_field_expr), field_type))
          fields
      in
      let typed_fields = List.map fst typed_fields_and_types in
      (* In a full system, we might want to create a unique struct type on the fly,
         or require struct definitions beforehand. For simplicity here, we just return a fresh TVar *)
      let typ = fresh_type_var () in
      (* Or could represent as TTuple or TRecord if we define those *)
      ({ expr = Struct typed_fields; typ }, typ)
  | RawTypeClassInstanceAccess (tc_name, func_name) ->
      let typeclass_signatures_raw = Hashtbl.find type_class_env tc_name in
      let function_signature_raw =
        List.assoc func_name typeclass_signatures_raw
      in
      (* Find signature for function *)
      let function_type =
        Ast_to_typed_ast.typannot_to_typ function_signature_raw
      in
      (* Resolve to typ *)
      let typ = function_type in
      ({ expr = TypeClassInstanceAccess (tc_name, func_name); typ }, typ)
  | RawBlock expr_list ->
      (* Handle RawBlock *)
      let block_env = env in
      (* Blocks create a new scope, but for now, let's use the same env - TODO: Deeper scope handling *)
      let typed_expr_list_and_types =
        List.map (fun expr -> typecheck_expr block_env expr) expr_list
      in
      let typed_expr_list = List.map fst typed_expr_list_and_types in
      let block_type =
        match List.rev typed_expr_list_and_types with
        | (_, last_type) :: _ ->
            last_type (* Type of block is type of last expression *)
        | [] -> TUnit (* Empty block has Unit type *)
      in
      ({ expr = Block typed_expr_list; typ = block_type }, block_type)

(* -------------------- Type Checking Patterns and Constructing Typed Patterns -------------------- *)

and typecheck_pattern env pattern expected_type : type_env * typedpattern =
  match pattern with
  | RawIntPattern i ->
      unify expected_type TInt;
      (env, IntPattern i)
  | RawBoolPattern b ->
      unify expected_type TBool;
      (env, BoolPattern b)
  | RawVarPattern name ->
      let env' = Env.add name expected_type env in
      (env', VarPattern name)
      (* Bind variable to expected type in the environment *)
  | RawListPattern patterns ->
      let element_type = fresh_type_var () in
      unify expected_type (TList element_type);
      (* Expected type must be a list *)
      let env', typed_patterns =
        List.fold_left
          (fun (current_env, typed_patterns) pattern' ->
            let env'', typed_pattern' =
              typecheck_pattern current_env pattern' element_type
            in
            (env'', typed_pattern' :: typed_patterns))
          (env, []) patterns
      in
      (env', ListPattern (List.rev typed_patterns))
  | RawWildcardPattern ->
      (env, WildcardPattern) (* Wildcard doesn't bind any variables *)
  | RawEnumPattern (enum_name, constructor_name, pattern_args) ->
    unify expected_type (TEnum enum_name);
    begin match Hashtbl.find_opt enum_defs enum_name with
    | Some constructors_def ->
        begin
            match List.assoc_opt constructor_name constructors_def with
            | Some expected_arg_types ->
                if List.length pattern_args <> List.length expected_arg_types then
                    error ("Enum pattern for constructor '" ^ constructor_name ^ "' of enum '" ^ enum_name ^ "' expects " ^ string_of_int (List.length expected_arg_types) ^ " arguments, but got " ^ string_of_int (List.length pattern_args)) None;
                let initial_acc : typ Env.t * typedpattern list = (env,[]) in
                let env', typed_pattern_args =
                    List.fold_left2
                        (fun (current_env, typed_pattern_args) pattern' expected_type' ->
                            let env'', typed_pattern' = typecheck_pattern current_env pattern' expected_type' in
                            (env'', typed_pattern' :: typed_pattern_args)
                        ) initial_acc pattern_args expected_arg_types
                in
                (env', EnumPattern (enum_name, constructor_name, List.rev typed_pattern_args))
            | None -> error ("Constructor '" ^ constructor_name ^ "' not found in enum '" ^ enum_name ^ "'") None
        end
    | None -> error ("Enum '" ^ enum_name ^ "' not found") None
    end
  | RawStructPattern pattern_fields -> (* Renamed 'fields' to 'pattern_fields' for clarity *)
    begin match expected_type with
    | TStruct struct_name ->
        begin
            match Hashtbl.find_opt struct_defs struct_name with
            | Some expected_fields_def ->
                let env', typed_fields =
                    List.fold_left
                        (fun (current_env, typed_fields) (field_name, field_pattern) ->
                            match List.assoc_opt field_name expected_fields_def with
                            | Some expected_type' ->
                                let env'', typed_field_pattern = typecheck_pattern current_env field_pattern expected_type' in
                                ((env''), (field_name, typed_field_pattern) :: typed_fields)
                            | None -> error ("Field '" ^ field_name ^ "' not found in struct '" ^ struct_name ^ "'") None
                        ) (env,[]) pattern_fields
                in
                (* Optional: Ensure all fields in the definition are covered by the pattern *)
                let pattern_field_names = List.map fst pattern_fields in
                let defined_field_names = List.map fst expected_fields_def in
                if List.sort compare pattern_field_names <> List.sort compare defined_field_names then
                    error ("Struct pattern for '" ^ struct_name ^ "' does not match the defined fields") None;
                (env', StructPattern (List.rev typed_fields))
            | None -> error ("Struct '" ^ struct_name ^ "' not found") None
        end
    | _ -> error "Struct pattern on non-struct type" None
    end
(* -------------------- Type Checking Top-Level Definitions -------------------- *)

let typecheck_top_level env (raw_top_level : raw_top_level) :
    type_env * typedtop_level =
  match raw_top_level with
  | RawFunDef (fun_name, _type_params, params, return_typ_annot, body_expr) ->
      (* Ignoring type_params for now *)
      let param_types_annot =
        List.map
          (fun (_param_name, typannot) ->
            Ast_to_typed_ast.typannot_to_typ typannot)
          params
      in
      let env_with_params =
        List.fold_left2
          (fun (acc_env : type_env) (param_name, _typannot) param_type ->
            Env.add param_name param_type acc_env)
          env params param_types_annot
      in
      let typed_body_expr, body_type =
        typecheck_expr env_with_params body_expr
      in
      let return_typ = Ast_to_typed_ast.typannot_to_typ return_typ_annot in
      unify body_type return_typ;
      let fun_type = TFun (param_types_annot, return_typ) in
      let typed_params =
        List.map
          (fun (p_name, typannot) ->
            (p_name, Ast_to_typed_ast.typannot_to_typ typannot))
          params
      in
      ( Env.add fun_name fun_type env,
        FunDef (fun_name, typed_params, return_typ, typed_body_expr) )
  | RawStructDef (name, fields) ->
      let typed_fields =
        List.map
          (fun (field_name, typannot) ->
            (field_name, Ast_to_typed_ast.typannot_to_typ typannot))
          fields
      in
      (* Store struct definition in a global struct environment if needed *)
      (env, StructDef (name, typed_fields))
  | RawEnumDef (name, constructors) ->
      let typed_constructors =
        List.map
          (fun (ctor_name, tyann_list) ->
            (ctor_name, List.map Ast_to_typed_ast.typannot_to_typ tyann_list))
          constructors
      in
      (* Store enum definition in a global enum environment if needed *)
      (env, EnumDef (name, typed_constructors))
  | RawTypeClassDef (name, function_signatures) ->
      let typed_function_signatures =
        List.map
          (fun (func_name, typannot) ->
            (func_name, Ast_to_typed_ast.typannot_to_typ typannot))
          function_signatures
      in
      Hashtbl.add type_class_env name function_signatures;
      (* Store raw signatures for now - consider storing typed sigs directly *)
      (env, TypeClassDef (name, typed_function_signatures))
  | RawInstanceDef (typeclass_name, type_annot, function_impls) ->
      let instance_type = Ast_to_typed_ast.typannot_to_typ type_annot in
      let typeclass_signatures_raw =
        Hashtbl.find type_class_env typeclass_name
      in
      (* Raw signatures *)

      let typed_function_impls_rev = ref [] in
      List.iter2
        (fun (func_name_sig, raw_sig_tyann) (func_name_impl, raw_func_expr) ->
          if func_name_sig <> func_name_impl then
            error
              ("Function name mismatch in instance definition for typeclass "
             ^ typeclass_name)
              None;

          let expected_func_type =
            Ast_to_typed_ast.typannot_to_typ raw_sig_tyann
          in
          (* Resolve raw signature to typ *)
          let typed_func_expr, actual_func_type =
            typecheck_expr env raw_func_expr
          in
          (* Typecheck implementation *)
          unify expected_func_type actual_func_type;
          (* MUST UNIFY! Ensure implementation matches signature *)
          typed_function_impls_rev :=
            (func_name_impl, typed_func_expr) :: !typed_function_impls_rev)
        typeclass_signatures_raw function_impls;

      let typed_function_impls = List.rev !typed_function_impls_rev in
      Hashtbl.add instance_env
        (typeclass_name, string_of_typ instance_type)
        typed_function_impls;
      (* Store typed instance *)
      (env, InstanceDef (typeclass_name, instance_type, typed_function_impls))

(* -------------------- Main Type Checking Function -------------------- *)

let typecheck_program (raw_top_levels : raw_top_level list) =
  (* let struct_defs = Hashtbl.create 10 in
  let enum_defs = Hashtbl.create 10 in *)
  let initial_env = Env.empty in
  Hashtbl.clear substitution_env;
  (* Clear substitution env for each program typechecking *)
  try
    let _, typed_top_levels =
      List.fold_left_map typecheck_top_level initial_env raw_top_levels
    in
    replace_typevars_program
      typed_top_levels (* Apply substitution at the end *)
  with TypeError (msg, loc_opt) ->
    let loc_str =
      match loc_opt with
      | Some loc -> Location.pretty_location loc ^ ": "
      | None -> ""
    in
    Printf.eprintf "%sType Error: %s\n" loc_str msg;
    exit 1
