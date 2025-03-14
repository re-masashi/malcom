(* typed_ast.ml *)

type typ =
  | TInt
  | TBool
  | TStr
  | TUnit
  | TList of typ
  | TFun of typ list * typ
  | TStruct of string
  | TEnum of string
  | TVar of string (* Type Variable *)
  | TGeneric of
      string
      * typ list (* Generic Type - List<Int> becomes TGeneric("List", [TInt]) *)
  | TConstrainedVar of
      string
      * string list (* Type Variable with constraints - 'a with ['Eq; 'Show'] *)
  | TTypeClass of string
(* Represents a typeclass itself as a type (for typeclass parameters, potentially) *)

type expr_t = { expr : expr; typ : typ }

and expr =
  | Int of int
  | Bool of bool
  | Str of string
  | Unit
  | Var of string * typ
  | Add of expr_t * expr_t
  | Sub of expr_t * expr_t
  | Mul of expr_t * expr_t
  | Div of expr_t * expr_t
  | Equal of expr_t * expr_t
  | LessThan of expr_t * expr_t
  | GreaterThan of expr_t * expr_t
  | Let of string * expr_t * expr_t
  | If of expr_t * expr_t * expr_t
  | Fun of string * expr_t
  | App of expr_t * expr_t
  | List of expr_t list
  | Match of expr_t * (typedpattern * expr_t) list
  | StructAccess of expr_t * string
  | Enum of string * string * expr_t list
  | EnumAccess of expr_t * int
  | Struct of (string * expr_t) list
  | TypeClassInstanceAccess of string * string (* Typed AST version *)
  | Block of expr_t list

and typedpattern =
  | IntPattern of int
  | BoolPattern of bool
  | VarPattern of string
  | ListPattern of typedpattern list
  | WildcardPattern
  | EnumPattern of string * string * typedpattern list
  | StructPattern of (string * typedpattern) list

type typedtop_level =
  | StructDef of string * (string * typ) list
  | EnumDef of string * (string * typ list) list
  | FunDef of string * (string * typ) list * typ * expr_t
  | TypeClassDef of string * (string * typ) list
    (* Typed version of typeclass def - functions have types now *)
  | InstanceDef of
      string * typ * (string * expr_t) list (* Typed version of instance def *)

type program = {
  structs : (string * (string * typ) list) list;
  enums : (string * (string * typ list) list) list;
  top_levels : typedtop_level list;
}

let enum_defs : (string, (string * typ list) list) Hashtbl.t = Hashtbl.create 10
let struct_defs : (string, (string * typ) list) Hashtbl.t = Hashtbl.create 10
