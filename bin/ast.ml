(* ast.ml *)
type raw_typannot =
  | TAInt
  | TABool
  | TAStr
  | TAUnit
  | TAList of raw_typannot
  | TAFun of raw_typannot list * raw_typannot
  | TAStruct of string
  | TAEnum of string
  | TAVar of string (* Type Variable for generics *)
  | TAGeneric of string * raw_typannot list (* Generic type e.g., List<'a> *)
  | TAConstraint of
      raw_typannot * string (* Typeclass constraint e.g., 'a : Eq *)

type raw_top_level =
  | RawStructDef of string * (string * raw_typannot) list
  | RawEnumDef of string * (string * raw_typannot list) list
  | RawFunDef of
      string
      * type_param_list
      * (string * raw_typannot) list
      * raw_typannot
      * raw_expr
  | RawTypeClassDef of
      string * (string * raw_typannot) list (* Define a typeclass *)
  | RawInstanceDef of
      string
      * raw_typannot
      * (string * raw_expr) list (* Instance of a typeclass *)

and type_param_list =
  string list (* List of type parameter names e.g., ['a; 'b] *)

and raw_expr =
  | RawInt of int
  | RawBool of bool
  | RawStr of string
  | RawUnit
  | RawVar of string
  | RawAdd of raw_expr * raw_expr
  | RawSub of raw_expr * raw_expr
  | RawMul of raw_expr * raw_expr
  | RawDiv of raw_expr * raw_expr
  | RawEqual of raw_expr * raw_expr
  | RawLessThan of raw_expr * raw_expr
  | RawGreaterThan of raw_expr * raw_expr
  | RawLet of string * raw_expr * raw_expr
  | RawIf of raw_expr * raw_expr * raw_expr
  | RawFun of string * raw_expr
  | RawApp of raw_expr * raw_expr
  | RawList of raw_expr list
  | RawMatch of raw_expr * (raw_pattern * raw_expr) list
  | RawStructAccess of raw_expr * string
  | RawEnum of string * string * raw_expr list
  | RawEnumAccess of raw_expr * int
  | RawStruct of (string * raw_expr) list
  | RawTypeClassInstanceAccess of
      string * string (* Access typeclass instance function - e.g., Eq.equals *)
  | RawBlock of raw_expr list

and raw_pattern =
  | RawIntPattern of int
  | RawBoolPattern of bool
  | RawVarPattern of string
  | RawListPattern of raw_pattern list
  | RawWildcardPattern
  | RawEnumPattern of string * string * raw_pattern list (*enum, constructor, pattern*)
  | RawStructPattern of (string * raw_pattern) list

type top_level = raw_top_level
type expr = raw_expr
type typannot = raw_typannot
type pattern = raw_pattern
