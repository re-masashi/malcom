(* location.ml *)

type t = { line : int; column : int; file : string }

let dummy = { line = -1; column = -1; file = "testfile.mom" }
(* Represents a dummy or unknown location *)

let pretty_location loc =
  Printf.sprintf "Line %d, Column %d, File %s" loc.line loc.column loc.file
