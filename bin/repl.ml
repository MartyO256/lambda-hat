open Lambda_hat
open Evaluation [@@warning "-33"]
open Syntax
open React

module Interpreter = struct
  type state = {
    prompt_number : Int.t;
    buffer : String.t List.t;
    signature : Signature.t;
    evaluation_environment : expression Identifier.Map.t;
    fresh_variable_state : Typing.Fresh_variable_state.t;
    typing_state : Typing.State.t;
  }

  let[@inline] prompt_number { prompt_number; _ } = prompt_number
  let[@inline] [@warning "-32"] buffer { buffer; _ } = buffer
  let[@inline] signature { signature; _ } = signature

  let[@inline] evaluation_environment { evaluation_environment; _ } =
    evaluation_environment

  let[@inline] fresh_variable_state { fresh_variable_state; _ } =
    fresh_variable_state

  let[@inline] typing_state { typing_state; _ } = typing_state

  let initial_state =
    {
      prompt_number = 1;
      buffer = [];
      signature = Syntax.empty_signature;
      evaluation_environment = Identifier.Map.empty;
      fresh_variable_state = Typing.Fresh_variable_state.initial_state;
      typing_state = Typing.State.initial_state Syntax.empty_signature;
    }

  let set_signature signature state = { state with signature }

  let set_fresh_variable_state fresh_variable_state state =
    { state with fresh_variable_state }

  let set_typing_state typing_state state = { state with typing_state }

  let add_to_typing_context identifier type_ state =
    {
      state with
      typing_state =
        Typing.State.extend_typing identifier type_ (typing_state state);
    }

  let reset_buffer state = { state with buffer = [] }
  let add_to_buffer line state = { state with buffer = line :: state.buffer }

  let increment_prompt_number state =
    { state with prompt_number = state.prompt_number + 1 }

  let next_state ?signature state =
    state |> reset_buffer |> increment_prompt_number
    |> set_signature (Option.value signature ~default:state.signature)

  let add_value identifier value state =
    {
      state with
      evaluation_environment =
        Identifier.Map.add identifier value state.evaluation_environment;
    }

  let suffix = ";;"

  let string_without_suffix input =
    String.sub input 0 (String.length input - String.length suffix)

  exception Parser_error of String.t

  let () =
    Printexc.register_printer (function
      | Parser_error message ->
          Option.some (Format.asprintf "Error during parsing: %s" message)
      | _ -> Option.none)

  let parse_declaration input =
    let declaration_parser = Parser.lex Parser.declaration in
    let result =
      Parser.parse_string ~consume:Parser.Consume.All declaration_parser input
    in
    match result with
    | Result.Ok declaration -> declaration
    | Result.Error cause -> raise (Parser_error cause)

  let evaluate_declaration state declaration =
    let signature' = Syntax.add_declaration (signature state) declaration in
    Validation.validate_declaration signature' declaration;
    match declaration with
    | Declaration.Value { identifier; expression } ->
        let fresh_variable_state', inferred_type =
          Typing.infer
            (fresh_variable_state state)
            (typing_state state) expression
        in
        let evaluated_expression =
          Evaluation.evaluate (evaluation_environment state) expression
        in
        let output =
          Format.asprintf "@[val %a = %a@]" Identifier.pp identifier
            Syntax.pp_expression evaluated_expression
        in
        let state' =
          state
          |> next_state ~signature:signature'
          |> add_value identifier evaluated_expression
          |> set_fresh_variable_state fresh_variable_state'
          |> set_typing_state
               (Typing.State.set_signature signature' (typing_state state))
          |> add_to_typing_context identifier inferred_type
        in
        (state', Option.some output)
    | Declaration.Datatype _ ->
        let state' =
          next_state ~signature:signature' state
          |> set_typing_state
               (Typing.State.set_signature signature' (typing_state state))
        in
        (state', Option.none)
    | declaration -> raise (Malformed_declaration declaration)

  let evaluate_input state input =
    try
      let trimmed_input = String.trim input in
      if String.ends_with ~suffix trimmed_input then
        let truncated_input = string_without_suffix trimmed_input in
        let reconstructed_input =
          String.concat "" (List.rev (truncated_input :: state.buffer))
        in
        let parsed_declaration = parse_declaration reconstructed_input in
        evaluate_declaration state parsed_declaration
      else (add_to_buffer input state, Option.none)
    with error -> (next_state state, Option.some (Printexc.to_string error))
end

module Repl = struct
  let make_prompt state =
    let prompt =
      Format.asprintf "In  [%d]: " (Interpreter.prompt_number state)
    in
    match state.Interpreter.buffer with
    | [] -> LTerm_text.eval [ S prompt ]
    | _ ->
        let blank_prompt = String.init (String.length prompt) (fun _ -> ' ') in
        LTerm_text.eval [ S blank_prompt ]

  let make_output state out =
    let output =
      Format.asprintf "Out [%d]: %s" (Interpreter.prompt_number state) out
    in
    LTerm_text.eval [ S output ]

  class read_line ~term ~history ~state =
    object (self)
      inherit LTerm_read_line.read_line ~history ()
      inherit [Zed_string.t] LTerm_read_line.term term
      method! show_box = false
      initializer self#set_prompt (S.const (make_prompt state))
    end

  let rec loop term history interpreter_state =
    let open Lwt in
    Lwt.catch
      (fun () ->
        let line_reader =
          new read_line
            ~term
            ~history:(LTerm_history.contents history)
            ~state:interpreter_state
        in
        line_reader#run >|= fun command -> Some command)
      (function Sys.Break -> return Option.none | cause -> Lwt.fail cause)
    >>= function
    | Some command -> (
        let command_utf8 = Zed_string.to_utf8 command in
        let s', out =
          Interpreter.evaluate_input interpreter_state command_utf8
        in
        match out with
        | Option.Some out ->
            LTerm.fprintls term (make_output interpreter_state out)
            >>= fun () ->
            LTerm_history.add history command;
            loop term history s'
        | Option.None ->
            LTerm_history.add history command;
            loop term history s')
    | None -> loop term history interpreter_state

  let main () =
    let open Lwt in
    LTerm_inputrc.load () >>= fun () ->
    Lwt.catch
      (fun () ->
        Lazy.force LTerm.stdout >>= fun term ->
        loop term (LTerm_history.create []) Interpreter.initial_state)
      (function
        | LTerm_read_line.Interrupt -> Lwt.return () | exn -> Lwt.fail exn)

  let run () = Lwt_main.run (main ())
end

let () = Repl.run ()
