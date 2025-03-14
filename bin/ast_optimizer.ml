open Typed_ast

let rec fold_constants_expr (typed_expr : expr_t) : expr_t =
  match typed_expr.expr with
  | Add (e1, e2) -> (
      let optimized_e1 = fold_constants_expr e1 in
      let optimized_e2 = fold_constants_expr e2 in
      match (optimized_e1.expr, optimized_e2.expr) with
      | Int i1, Int i2 ->
          { typed_expr with expr = Int (i1 + i2) } (* Constant folding *)
      | _, Int 0 -> optimized_e1 (* Algebraic: x + 0 -> x *)
      | Int 0, _ -> optimized_e2 (* Algebraic: 0 + x -> x *)
      | _ -> { typed_expr with expr = Add (optimized_e1, optimized_e2) })
  | Sub (e1, e2) -> (
      let optimized_e1 = fold_constants_expr e1 in
      let optimized_e2 = fold_constants_expr e2 in
      match (optimized_e1.expr, optimized_e2.expr) with
      | Int i1, Int i2 ->
          { typed_expr with expr = Int (i1 - i2) } (* Constant folding *)
      | _, Int 0 -> optimized_e1 (* Algebraic: x - 0 -> x *)
      (* | Int 0, _ -> { typed_expr with expr = Int (- (int_value optimized_e2))} (* Algebraic: 0 - x -> -x, need helper int_value function *) *)
      | _ -> { typed_expr with expr = Sub (optimized_e1, optimized_e2) })
  | Mul (e1, e2) -> (
      let optimized_e1 = fold_constants_expr e1 in
      let optimized_e2 = fold_constants_expr e2 in
      match (optimized_e1.expr, optimized_e2.expr) with
      | Int i1, Int i2 ->
          { typed_expr with expr = Int (i1 * i2) } (* Constant folding *)
      | _, Int 1 -> optimized_e1 (* Algebraic: x * 1 -> x *)
      | Int 1, _ -> optimized_e2 (* Algebraic: 1 * x -> x *)
      | _, Int 0 | Int 0, _ ->
          { typed_expr with expr = Int 0 }
          (* Algebraic: x * 0 -> 0 and 0 * x -> 0 *)
      | _ -> { typed_expr with expr = Mul (optimized_e1, optimized_e2) })
  | Div (e1, e2) -> (
      let optimized_e1 = fold_constants_expr e1 in
      let optimized_e2 = fold_constants_expr e2 in
      match (optimized_e1.expr, optimized_e2.expr) with
      | Int i1, Int i2 ->
          if i2 = 0 then typed_expr (* Avoid division by zero *)
          else { typed_expr with expr = Int (i1 / i2) } (* Constant folding *)
      | _, Int 1 -> optimized_e1 (* Algebraic: x / 1 -> x *)
      | _ -> { typed_expr with expr = Div (optimized_e1, optimized_e2) })
  | Equal (e1, e2) | LessThan (e1, e2) | GreaterThan (e1, e2) -> (
      let optimized_e1 = fold_constants_expr e1 in
      let optimized_e2 = fold_constants_expr e2 in
      match (optimized_e1.expr, optimized_e2.expr) with
      | Int i1, Int i2 -> (
          (* Both operands are constant integers *)
          match typed_expr.expr with
          | Equal _ -> { typed_expr with expr = Bool (i1 = i2) }
          | LessThan _ -> { typed_expr with expr = Bool (i1 < i2) }
          | GreaterThan _ -> { typed_expr with expr = Bool (i1 > i2) }
          | _ ->
              { typed_expr with expr = typed_expr.expr } (* Should not happen *)
          )
      | Bool b1, Bool b2 -> (
          (* Both operands are constant booleans *)
          match typed_expr.expr with
          | Equal _ -> { typed_expr with expr = Bool (b1 = b2) }
          | _ ->
              { typed_expr with expr = typed_expr.expr } (* Should not happen *)
          )
      | _ -> { typed_expr with expr = typed_expr.expr })
  | If (cond, then_branch, else_branch) -> (
      let optimized_cond = fold_constants_expr cond in
      let optimized_then_branch = fold_constants_expr then_branch in
      let optimized_else_branch = fold_constants_expr else_branch in
      match optimized_cond.expr with
      | Bool true ->
          optimized_then_branch
          (* If condition is statically true, replace if with then-branch *)
      | Bool false ->
          optimized_else_branch
          (* If condition is statically false, replace with else-branch *)
      | _ ->
          {
            typed_expr with
            expr =
              If (optimized_cond, optimized_then_branch, optimized_else_branch);
          }
      (* Condition is not a constant boolean, cannot fold *))
  | Let (name, value, body) ->
      let optimized_value = fold_constants_expr value in
      let optimized_body = fold_constants_expr body in
      { typed_expr with expr = Let (name, optimized_value, optimized_body) }
  | App (fun_expr, args) ->
      let optimized_fun_expr = fold_constants_expr fun_expr in
      let optimized_args = fold_constants_expr args in
      { typed_expr with expr = App (optimized_fun_expr, optimized_args) }
  | List exprs ->
      let optimized_exprs = List.map fold_constants_expr exprs in
      { typed_expr with expr = List optimized_exprs }
  | Struct fields ->
      let optimized_fields =
        List.map (fun (fname, expr) -> (fname, fold_constants_expr expr)) fields
      in
      { typed_expr with expr = Struct optimized_fields }
  | StructAccess (expr, field_name) ->
      let optimized_expr = fold_constants_expr expr in
      { typed_expr with expr = StructAccess (optimized_expr, field_name) }
  | Enum (enum_name, constructor_name, args) ->
      let optimized_args = List.map fold_constants_expr args in
      {
        typed_expr with
        expr = Enum (enum_name, constructor_name, optimized_args);
      }
  | EnumAccess (expr, case_index) ->
      let optimized_expr = fold_constants_expr expr in
      { typed_expr with expr = EnumAccess (optimized_expr, case_index) }
  | Var _ | Int _ | Bool _ | Str _ | Unit | TypeClassInstanceAccess _ ->
      typed_expr
      (* These are already constants or vars, no folding needed directly *)
  | Match _ | Fun _ -> typed_expr (* Cases we are not yet optimizing further *)
  | Block exprs ->
      let optimized_exprs = List.map fold_constants_expr exprs in
      { typed_expr with expr = Block optimized_exprs }

let rec copy_propagation_expr (typed_expr : expr_t) : expr_t =
  let rec count_variable_uses name expr =
    match expr.expr with
    | Var (v_name, _) when v_name = name -> 1
    | Add (e1, e2)
    | Sub (e1, e2)
    | Mul (e1, e2)
    | Div (e1, e2)
    | Equal (e1, e2)
    | LessThan (e1, e2)
    | GreaterThan (e1, e2) (* | And (e1, e2) | Or (e1, e2)  *) ->
        count_variable_uses name e1 + count_variable_uses name e2
    | If (cond, then_branch, else_branch) ->
        count_variable_uses name cond
        + count_variable_uses name then_branch
        + count_variable_uses name else_branch
    | Let (_, value_expr, body_expr) ->
        count_variable_uses name value_expr + count_variable_uses name body_expr
    | App (fun_expr, args) ->
        count_variable_uses name fun_expr + count_variable_uses name args
    | List exprs ->
        List.fold_left
          (fun acc expr -> acc + count_variable_uses name expr)
          0 exprs
    | Struct fields ->
        List.fold_left
          (fun acc (_, expr) -> acc + count_variable_uses name expr)
          0 fields
    | StructAccess (expr, _) -> count_variable_uses name expr
    | Enum (_, _, args) ->
        List.fold_left
          (fun acc expr -> acc + count_variable_uses name expr)
          0 args
    | EnumAccess (expr, _) -> count_variable_uses name expr
    (* | Not expr -> count_variable_uses name expr *)
    | Block exprs ->
        List.fold_left
          (fun acc expr -> acc + count_variable_uses name expr)
          0 exprs
    | Fun (_, body_expr) ->
        count_variable_uses name body_expr (* Consider function body usage *)
    | Match (match_expr, cases) ->
        count_variable_uses name match_expr
        + List.fold_left
            (fun acc (_, case_expr) -> acc + count_variable_uses name case_expr)
            0 cases
    | Var _ | Int _ | Bool _ | Str _ | Unit | TypeClassInstanceAccess _
    (* | Enum _ | Struct _   *) ->
        0
    (* No variables in these *)
    (* | _ -> 0 (* Default case, to be safe *) *)
  in

  match typed_expr.expr with
  | Let (name, value_expr, body_expr) -> (
      let optimized_value_expr = copy_propagation_expr value_expr in
      let optimized_body_expr = copy_propagation_expr body_expr in
      match optimized_value_expr.expr with
      | Int _ | Bool _ | Str _ | Unit | Var _ ->
          (* Simple value: constant or variable *)
          if count_variable_uses name optimized_body_expr <= 1 then
            (* Used at most once in body *)
            match optimized_body_expr.expr with
            | Block exprs ->
                (* If body is a block, substitute in each expr of the block *)
                let substituted_exprs =
                  List.map
                    (fun expr ->
                      substitute_var_expr name optimized_value_expr expr)
                    exprs
                in
                { typed_expr with expr = Block substituted_exprs }
            | _ ->
                (* Otherwise, substitute directly in the body expression *)
                substitute_var_expr name optimized_value_expr
                  optimized_body_expr
          else
            {
              typed_expr with
              expr = Let (name, optimized_value_expr, optimized_body_expr);
            }
            (* Don't substitute if used more than once (for this simple version) *)
      | _ ->
          {
            typed_expr with
            expr = Let (name, optimized_value_expr, optimized_body_expr);
          }
      (* Don't substitute for complex values in this simple version *))
  | Add (e1, e2) ->
      {
        typed_expr with
        expr = Add (copy_propagation_expr e1, copy_propagation_expr e2);
      }
  | Sub (e1, e2) ->
      {
        typed_expr with
        expr = Sub (copy_propagation_expr e1, copy_propagation_expr e2);
      }
  | Mul (e1, e2) ->
      {
        typed_expr with
        expr = Mul (copy_propagation_expr e1, copy_propagation_expr e2);
      }
  | Div (e1, e2) ->
      {
        typed_expr with
        expr = Div (copy_propagation_expr e1, copy_propagation_expr e2);
      }
  | Equal (e1, e2) ->
      {
        typed_expr with
        expr = Equal (copy_propagation_expr e1, copy_propagation_expr e2);
      }
  | LessThan (e1, e2) ->
      {
        typed_expr with
        expr = LessThan (copy_propagation_expr e1, copy_propagation_expr e2);
      }
  | GreaterThan (e1, e2) ->
      {
        typed_expr with
        expr = GreaterThan (copy_propagation_expr e1, copy_propagation_expr e2);
      }
  (* | And (e1, e2) -> { typed_expr with expr = And (copy_propagation_expr e1, copy_propagation_expr e2) } *)
  (* | Or (e1, e2) -> { typed_expr with expr = Or (copy_propagation_expr e1, copy_propagation_expr e2) } *)
  (* | Not e -> { typed_expr with expr = Not (copy_propagation_expr e) } *)
  | If (cond, then_branch, else_branch) ->
      {
        typed_expr with
        expr =
          If
            ( copy_propagation_expr cond,
              copy_propagation_expr then_branch,
              copy_propagation_expr else_branch );
      }
  | App (fun_expr, args) ->
      {
        typed_expr with
        expr = App (copy_propagation_expr fun_expr, copy_propagation_expr args);
      }
  | List exprs ->
      { typed_expr with expr = List (List.map copy_propagation_expr exprs) }
  | Struct fields ->
      {
        typed_expr with
        expr =
          Struct
            (List.map
               (fun (fname, expr) -> (fname, copy_propagation_expr expr))
               fields);
      }
  | StructAccess (expr, field_name) ->
      {
        typed_expr with
        expr = StructAccess (copy_propagation_expr expr, field_name);
      }
  | Enum (enum_name, constructor_name, args) ->
      {
        typed_expr with
        expr =
          Enum (enum_name, constructor_name, List.map copy_propagation_expr args);
      }
  | EnumAccess (expr, case_index) ->
      {
        typed_expr with
        expr = EnumAccess (copy_propagation_expr expr, case_index);
      }
  | Block exprs ->
      { typed_expr with expr = Block (List.map copy_propagation_expr exprs) }
  | Fun (param_name, body_expr) ->
      {
        typed_expr with
        expr = Fun (param_name, copy_propagation_expr body_expr);
      }
  | Match (match_expr, cases) ->
      let optimized_cases =
        List.map
          (fun (pattern, case_expr) ->
            (pattern, copy_propagation_expr case_expr))
          cases
      in
      {
        typed_expr with
        expr = Match (copy_propagation_expr match_expr, optimized_cases);
      }
  | Var _ | Int _ | Bool _ | Str _ | Unit | TypeClassInstanceAccess _ ->
      typed_expr

and substitute_var_expr var_name value_expr target_expr : expr_t =
  match target_expr.expr with
  | Var (name, _typ) when name = var_name ->
      { expr = value_expr.expr; typ = value_expr.typ }
      (* Substitution happens here *)
  | Add (e1, e2) ->
      {
        target_expr with
        expr =
          Add
            ( substitute_var_expr var_name value_expr e1,
              substitute_var_expr var_name value_expr e2 );
      }
  | Sub (e1, e2) ->
      {
        target_expr with
        expr =
          Sub
            ( substitute_var_expr var_name value_expr e1,
              substitute_var_expr var_name value_expr e2 );
      }
  | Mul (e1, e2) ->
      {
        target_expr with
        expr =
          Mul
            ( substitute_var_expr var_name value_expr e1,
              substitute_var_expr var_name value_expr e2 );
      }
  | Div (e1, e2) ->
      {
        target_expr with
        expr =
          Div
            ( substitute_var_expr var_name value_expr e1,
              substitute_var_expr var_name value_expr e2 );
      }
  | Equal (e1, e2) ->
      {
        target_expr with
        expr =
          Equal
            ( substitute_var_expr var_name value_expr e1,
              substitute_var_expr var_name value_expr e2 );
      }
  | LessThan (e1, e2) ->
      {
        target_expr with
        expr =
          LessThan
            ( substitute_var_expr var_name value_expr e1,
              substitute_var_expr var_name value_expr e2 );
      }
  | GreaterThan (e1, e2) ->
      {
        target_expr with
        expr =
          GreaterThan
            ( substitute_var_expr var_name value_expr e1,
              substitute_var_expr var_name value_expr e2 );
      }
  (* | And (e1, e2) -> { target_expr with expr = And (substitute_var_expr var_name value_expr e1, substitute_var_expr var_name value_expr e2) } *)
  (* | Or (e1, e2) -> { target_expr with expr = Or (substitute_var_expr var_name value_expr e1, substitute_var_expr var_name value_expr e2) } *)
  (* | Not e -> { target_expr with expr = Not (substitute_var_expr var_name value_expr e) } *)
  | If (cond, then_branch, else_branch) ->
      {
        target_expr with
        expr =
          If
            ( substitute_var_expr var_name value_expr cond,
              substitute_var_expr var_name value_expr then_branch,
              substitute_var_expr var_name value_expr else_branch );
      }
  | Let (name, val_expr, body_expr) ->
      (* IMPORTANT: Don't substitute in the 'name' of the Let binding itself! *)
      {
        target_expr with
        expr =
          Let
            ( name,
              substitute_var_expr var_name value_expr val_expr,
              substitute_var_expr var_name value_expr body_expr );
      }
  | App (fun_expr, args) ->
      {
        target_expr with
        expr = App (substitute_var_expr var_name value_expr fun_expr, args);
      }
  | List exprs ->
      {
        target_expr with
        expr = List (List.map (substitute_var_expr var_name value_expr) exprs);
      }
  | Struct fields ->
      {
        target_expr with
        expr =
          Struct
            (List.map
               (fun (fname, expr) ->
                 (fname, substitute_var_expr var_name value_expr expr))
               fields);
      }
  | StructAccess (expr, field_name) ->
      {
        target_expr with
        expr =
          StructAccess (substitute_var_expr var_name value_expr expr, field_name);
      }
  | Enum (enum_name, constructor_name, args) ->
      {
        target_expr with
        expr =
          Enum
            ( enum_name,
              constructor_name,
              List.map (substitute_var_expr var_name value_expr) args );
      }
  | EnumAccess (expr, case_index) ->
      {
        target_expr with
        expr =
          EnumAccess (substitute_var_expr var_name value_expr expr, case_index);
      }
  | Block exprs ->
      {
        target_expr with
        expr = Block (List.map (substitute_var_expr var_name value_expr) exprs);
      }
  | Fun (param_name, body_expr) ->
      (* IMPORTANT: Don't substitute if var_name is same as param_name (shadowing) *)
      if param_name = var_name then target_expr
        (* Don't substitute into function parameter scope if names clash *)
      else
        {
          target_expr with
          expr =
            Fun (param_name, substitute_var_expr var_name value_expr body_expr);
        }
  | Match (match_expr, cases) ->
      let substituted_cases =
        List.map
          (fun (pattern, case_expr) ->
            (* For simplicity in this example, not handling pattern-bound variables and substitution *)
            (pattern, substitute_var_expr var_name value_expr case_expr))
          cases
      in
      {
        target_expr with
        expr =
          Match
            ( substitute_var_expr var_name value_expr match_expr,
              substituted_cases );
      }
  | Var _ | Int _ | Bool _ | Str _ | Unit | TypeClassInstanceAccess _ ->
      target_expr
(* No further substitution needed in these base cases *)
(* | _ -> target_expr (* Default case, to be safe *) *)

let fold_constants_program typed_program =
  List.map
    (fun top_level ->
      match top_level with
      | FunDef (name, params, return_typ, body_expr) ->
          let folded_body_expr = fold_constants_expr body_expr in
          FunDef (name, params, return_typ, folded_body_expr)
      | other_top_level -> other_top_level)
    typed_program

let simplify_algebraic_program typed_program =
  List.map
    (fun top_level ->
      match top_level with
      | FunDef (name, params, return_typ, body_expr) ->
          let simplified_body_expr = fold_constants_expr body_expr in
          (* For now reuse constant folder since algebraic simplifications are added there *)
          FunDef (name, params, return_typ, simplified_body_expr)
      | other_top_level -> other_top_level)
    typed_program

let simplify_boolean_program typed_program =
  List.map
    (fun top_level ->
      match top_level with
      | FunDef (name, params, return_typ, body_expr) ->
          let simplified_body_expr = fold_constants_expr body_expr in
          (* For now reuse constant folder as boolean simplifications are there *)
          FunDef (name, params, return_typ, simplified_body_expr)
      | other_top_level -> other_top_level)
    typed_program

let copy_propagation_program typed_program =
  List.map
    (fun top_level ->
      match top_level with
      | FunDef (name, params, return_typ, body_expr) ->
          let propagated_body_expr = copy_propagation_expr body_expr in
          FunDef (name, params, return_typ, propagated_body_expr)
      | other_top_level -> other_top_level)
    typed_program

let optimize_program (typed_program : typedtop_level list) : typedtop_level list
    =
  let optimized_top_levels =
    List.map
      (fun top_level ->
        match top_level with
        | FunDef (name, params, return_typ, body_expr) ->
            let folded_body_expr = fold_constants_expr body_expr in
            (* Constant folding first *)
            let alg_simplified_body_expr =
              fold_constants_expr folded_body_expr
            in
            (* Algebraic simplification (can reuse fold_constants for now if rules are within it) *)
            let bool_simplified_body_expr =
              fold_constants_expr alg_simplified_body_expr
            in
            (* Boolean simplification (also in fold_constants) *)
            let copy_propagated_body_expr =
              copy_propagation_expr bool_simplified_body_expr
            in
            (* Copy propagation after other simplifications *)

            FunDef (name, params, return_typ, copy_propagated_body_expr)
            (* Return the result of optimizations *)
        | StructDef _ | EnumDef _ | TypeClassDef _ | InstanceDef _ -> top_level
        (* For now, only optimize function bodies, leave other top-levels unchanged *))
      typed_program
  in
  optimized_top_levels
