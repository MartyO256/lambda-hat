open Syntax_definition

let guard_constructor_application expression =
  let rec guard_constructor_application expression arguments =
    match expression with
    | Expression.Constructor { identifier } ->
        Option.some (identifier, arguments)
    | Expression.Application { applicand; argument } ->
        guard_constructor_application applicand (argument :: arguments)
    | _ -> Option.none
  in
  guard_constructor_application expression []

let is_constructor_application expression =
  Option.is_some (guard_constructor_application expression)

type evaluation_state = expression Identifier.Map.t

exception Free_variable of Identifier.t
exception Invalid_applicand of expression
exception Invalid_rec of expression
exception Invalid_case_analysis of expression
exception Inexhaustive_case_analysis of expression

let[@warning "-32"] print_state state =
  Format.fprintf Format.std_formatter "{@;%a@;}@."
    (Format.pp_print_list
       ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@ ")
       (fun ppf (identifier, value) ->
         Format.fprintf ppf "%a :@ %a" Identifier.pp identifier
           Syntax_pp.pp_expression value))
    (Identifier.Map.bindings state)

let rec evaluate state expression =
  match expression with
  | Expression.Variable { identifier } -> (
      match Identifier.Map.find_opt identifier state with
      | Option.None -> raise (Free_variable identifier)
      | Option.Some expression -> expression)
  | Expression.Constructor _ -> expression
  | Expression.Abstraction _ ->
      Syntax_constructors.make_expression_closure ~expression ~environment:state
  | Expression.Closure { expression; environment } ->
      let state' = Identifier.Map.fold Identifier.Map.add environment state in
      evaluate state' expression
  | Expression.Rec _ ->
      Syntax_constructors.make_expression_closure ~expression ~environment:state
  | Expression.Case { scrutinee; branches } (* ι-reduction *) -> (
      let scrutinee' = evaluate state scrutinee in
      match guard_constructor_application scrutinee' with
      | Option.Some (constructor, arguments) -> (
          match
            List.find_map
              (fun (constructor', body) ->
                if Identifier.equal constructor constructor' then
                  Option.some body
                else Option.none)
              branches
          with
          | Option.Some body ->
              let expression =
                List.fold_left
                  (fun applicand argument ->
                    Syntax_constructors.make_expression_application ~applicand
                      ~argument)
                  body arguments
              in
              evaluate state expression
          | Option.None -> raise (Inexhaustive_case_analysis expression))
      | Option.None -> raise (Invalid_case_analysis expression))
  | Expression.Application { applicand; argument } -> (
      match evaluate state applicand with
      | Expression.Closure
          {
            expression =
              Expression.Abstraction { parameter_identifier; body; _ };
            environment;
          }
      (* β-reduction *) ->
          let argument' = evaluate state argument in
          let state' =
            Identifier.Map.fold Identifier.Map.add environment state
          in
          let state'' =
            Identifier.Map.add parameter_identifier argument' state'
          in
          evaluate state'' body
      | Expression.Abstraction { parameter_identifier; body; _ }
      (* β-reduction *) ->
          let argument' = evaluate state argument in
          let state' =
            Identifier.Map.add parameter_identifier argument' state
          in
          evaluate state' body
      | Expression.Closure
          {
            expression =
              Expression.Rec { identifier; expression = inner_expression; _ } as
              applicand;
            environment;
          }
      (* µ-reduction *) -> (
          let argument' = evaluate state argument in
          match guard_constructor_application argument' with
          | Option.Some _ ->
              let state' =
                Identifier.Map.fold Identifier.Map.add environment state
              in
              let state'' = Identifier.Map.add identifier applicand state' in
              let expression' =
                Syntax_constructors.make_expression_application
                  ~applicand:inner_expression ~argument:argument'
              in
              evaluate state'' expression'
          | Option.None -> raise (Invalid_rec expression))
      | Expression.Rec { identifier; expression = inner_expression; _ } as
        applicand
      (* µ-reduction *) -> (
          let argument' = evaluate state argument in
          match guard_constructor_application argument' with
          | Option.Some _ ->
              let state' = Identifier.Map.add identifier applicand state in
              let expression' =
                Syntax_constructors.make_expression_application
                  ~applicand:inner_expression ~argument:argument'
              in
              evaluate state' expression'
          | Option.None -> raise (Invalid_rec expression))
      | Expression.Constructor _ as applicand ->
          let argument' = evaluate state argument in
          Syntax_constructors.make_expression_application ~applicand
            ~argument:argument'
      | Expression.Application { applicand; argument = subargument }
        when is_constructor_application applicand ->
          let applicand' = evaluate state applicand in
          let argument' = evaluate state argument in
          let subargument' = evaluate state subargument in
          Syntax_constructors.make_expression_application
            ~applicand:
              (Syntax_constructors.make_expression_application
                 ~applicand:applicand' ~argument:subargument')
            ~argument:argument'
      | applicand -> raise (Invalid_applicand applicand))
  | Expression.Annotated { expression; _ } -> evaluate state expression

let () =
  Printexc.register_printer (function
    | Free_variable variable ->
        Option.some
          (Format.asprintf "Free variable @[%a@] encountered during evaluation"
             Identifier.pp variable)
    | Invalid_applicand applicand ->
        Option.some
          (Format.asprintf
             "Invalid applicand @[%a@] encountered during evaluation"
             Syntax_pp.pp_expression applicand)
    | Invalid_rec expression ->
        Option.some
          (Format.asprintf
             "Invalid recursive expression @[%a@] encountered during evaluation"
             Syntax_pp.pp_expression expression)
    | Invalid_case_analysis expression ->
        Option.some
          (Format.asprintf
             "Invalid case analysis expression @[%a@] encountered during \
              evaluation"
             Syntax_pp.pp_expression expression)
    | Inexhaustive_case_analysis expression ->
        Option.some
          (Format.asprintf
             "Inexhaustive case analysis expression @[%a@] encountered during \
              evaluation"
             Syntax_pp.pp_expression expression)
    | _ -> Option.none)
