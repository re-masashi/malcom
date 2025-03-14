(* Simplified MIR with explicit types and SSA-like form *)
type primitive_type =
  | TInt
  | TBool
  | TUnit
  | TPtr of primitive_type (* For structs/enums *)

type operand =
  | ConstInt of int
  | ConstBool of bool
  | Temp of int
  | Global of string

type instruction =
  | Assign of int * prim_operation (* dest_temp, operation *)
  | Store of operand * operand (* value, target *)
  | Load of int * operand (* dest_temp, source *)

and prim_operation =
  | Add of operand * operand
  | Sub of operand * operand
  | Mul of operand * operand
  | ICmpEq of operand * operand
  | Call of string * operand list
  | GEP of operand * int list (* Get element pointer for structs *)

type terminator = 
  | Ret of operand
  | Jmp of string
  | CondJmp of operand * string * string (* condition, then_label, else_label *)

type block = {
  label : string;
  instructions : instruction list;
  terminator : terminator;
}

type function_def = {
  name : string;
  params : (string * primitive_type) list;
  return_type : primitive_type;
  blocks : block list;
}

type mir_program = {
  structs : (string * primitive_type list) list;
  functions : function_def list;
}