(* main.ml *)
open Arg
open Ast
open Typed_ast
open Ast_optimizer

(* open Ast_to_typed_ast *)
open Typechecker
open Utils

let input_file = ref ""
let output_file = ref "a.out"
let optimize = ref false
let verbose = ref false
let usage_msg = "malcom [options] <input_file>"

let arg_spec =
  [
    ("-o", Set_string output_file, "Set output file");
    ("-O", Set optimize, "Enable optimizations");
    ("-v", Set verbose, "Enable verbose output");
    ( "-h",
      Unit
        (fun () ->
          print_endline usage_msg;
          exit 0),
      "Display this help message" );
  ]

let anonymous_arg filename =
  if !input_file = "" then input_file := filename
  else raise (Bad "Only one input file allowed")

let () =
  try
    parse arg_spec anonymous_arg usage_msg;
    if !input_file = "" then raise (Bad "Input file required");
    Printf.printf "Input file: %s\n" !input_file;
    Printf.printf "Output file: %s\n" !output_file;
    Printf.printf "Optimize: %b\n" !optimize;
    Printf.printf "Verbose: %b\n" !verbose;

    (* Sample AST with type annotations *)
    let sample_ast : top_level =
      RawFunDef
        ( "add_one",
          [],
          (* Type parameters list - empty for this simple function *)
          [ ("x", TAVar "a") ],
          (* Parameters list: x of type Int *)
          TAVar "b",
          (* Return type: Int *)
          RawAdd (RawVar "x", RawInt 1)
          (* RawIf(RawBool false, RawSub (RawInt 1, RawInt 1), RawAdd (RawInt 1, RawInt 2)) (* Function body *) *)
        )
      (*   RawFunDef (
          "apply_to_int",
           [],
           [
            ("f", TAFun ([TAInt], TAVar "result"));  
            ("x", TAInt)
          ],
          TAVar "result",
          RawApp (RawVar "f", RawVar "x") 
       ) *)
    in

    print_endline "Raw AST:";
    print_top_level sample_ast;

    print_endline "type checking...";
    let inferred_typed_ast : typedtop_level list =
      typecheck_program [ sample_ast ]
    in
    print_endline "type checked!";

    print_endline "Inferred Typed AST:";
    List.iter
      (fun typed_top_level ->
        print_typed_top_level typed_top_level;
        print_newline ())
      inferred_typed_ast;

    print_endline "Optimized Typed AST:";
    let optimized_ast = optimize_program inferred_typed_ast in
    List.iter
      (fun typed_top_level ->
        print_typed_top_level typed_top_level;
        print_newline ())
      optimized_ast;

    (* Sample AST demonstrating Type Inference - List Head function *)
    let inference_list_ast : top_level =
      RawFunDef
        ( "head",
          [],
          (* No type parameters *)
          [ ("list", TAVar "a") ],
          (* Parameter 'list' with empty type annotation - request inference *)
          TAVar "a",
          (* Return type also to be inferred *)
          RawMatch
            ( RawVar "list",
              [
                (RawListPattern [], RawUnit);
                (* Case for empty list - return unit for simplicity *)
                ( RawListPattern [ RawVarPattern "head_val"; RawWildcardPattern ],
                  RawVar "head_val" )
                (* Case for non-empty list - return head_val *);
              ] ) )
    in

    print_endline "\n--- Program with List Inference Example ---";
    print_endline "Raw AST (List Inference Example):";
    print_top_level inference_list_ast;

    print_endline "Type checking (List Inference Example)...";
    let inferred_typed_ast_list_inference : typedtop_level list =
      typecheck_program [ inference_list_ast ]
    in
    print_endline "Type checked! (List Inference Example)";

    print_endline "Inferred Typed AST (List Inference Example):";
    List.iter
      (fun typed_top_level ->
        print_typed_top_level typed_top_level;
        print_newline ())
      inferred_typed_ast_list_inference
  with Bad msg ->
    Printf.eprintf "Error: %s\n" msg;
    Printf.eprintf "%s\n" usage_msg;
    exit 1
