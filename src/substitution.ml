open Syntax_definition

type stage_substitution = stage Identifier.Map.t
type type_substitution = type_ Identifier.Map.t
type expression_substitution = expression Identifier.Map.t

type substitution =
  [ `Stage of stage | `Type of type_ | `Expression of expression ]
  Identifier.Map.t

let empty_substitution = Identifier.Map.empty

let lift_stage_substitution substitution =
  Identifier.Map.map (fun stage -> `Stage stage) substitution

let lift_type_substitution substitution =
  Identifier.Map.map (fun type_ -> `Type type_) substitution

let lift_expression_substitution substitution =
  Identifier.Map.map (fun expression -> `Expression expression) substitution

exception
  Invalid_stage_substitution of {
    substitution : substitution;
    identifier : identifier;
  }

exception
  Invalid_type_substitution of {
    substitution : substitution;
    identifier : identifier;
  }

exception
  Invalid_expression_substitution of {
    substitution : substitution;
    identifier : identifier;
  }

let rec apply_substitution_stage substitution stage =
  match stage with
  | Stage.Variable { identifier } -> (
      match Identifier.Map.find_opt identifier substitution with
      | Option.Some (`Stage stage') -> stage'
      | Option.Some _ ->
          raise (Invalid_stage_substitution { substitution; identifier })
      | Option.None -> stage)
  | Stage.Successor { stage } ->
      let stage' = apply_substitution_stage substitution stage in
      Syntax_constructors.make_stage_successor stage'
  | Stage.Infinity -> stage
  | Stage.Closure { stage; environment } ->
      let stage_substitution = lift_stage_substitution environment in
      let substitution' =
        Identifier.Map.fold Identifier.Map.add substitution stage_substitution
      in
      apply_substitution_stage substitution' stage

and apply_substitution_type substitution type_ =
  match type_ with
  | Type.Variable { identifier } -> (
      match Identifier.Map.find_opt identifier substitution with
      | Option.Some (`Type type_') -> type_'
      | Option.Some _ ->
          raise (Invalid_type_substitution { substitution; identifier })
      | Option.None -> type_)
  | Type.Arrow { domain; range } ->
      let domain' = apply_substitution_type substitution domain
      and range' = apply_substitution_type substitution range in
      Syntax_constructors.make_type_arrow ~domain:domain' ~range:range'
  | Type.Datatype { identifier; stage; arguments } ->
      let stage' = apply_substitution_stage substitution stage
      and arguments' =
        List.map (apply_substitution_type substitution) arguments
      in
      Syntax_constructors.make_type_datatype ~identifier ~stage:stage'
        ~arguments:arguments'
  | Type.Closure { type_; environment } ->
      let type_substitution = lift_type_substitution environment in
      let substitution' =
        Identifier.Map.fold Identifier.Map.add substitution type_substitution
      in
      apply_substitution_type substitution' type_

and apply_substitution_expression substitution expression =
  match expression with
  | Expression.Variable { identifier } -> (
      match Identifier.Map.find_opt identifier substitution with
      | Option.Some (`Expression expression') -> expression'
      | Option.Some _ ->
          raise (Invalid_expression_substitution { substitution; identifier })
      | Option.None -> expression)
  | Expression.Constructor _ -> expression
  | Expression.Abstraction { parameter_identifier; parameter_type; body } ->
      let parameter_type' =
        Option.map (apply_substitution_type substitution) parameter_type
      in
      let substitution' =
        Identifier.Map.remove parameter_identifier substitution
      in
      let body' = apply_substitution_expression substitution' body in
      Syntax_constructors.make_expression_abstraction ~parameter_identifier
        ~parameter_type:parameter_type' ~body:body'
  | Expression.Application { applicand; argument } ->
      let applicand' = apply_substitution_expression substitution applicand
      and argument' = apply_substitution_expression substitution argument in
      Syntax_constructors.make_expression_application ~applicand:applicand'
        ~argument:argument'
  | Expression.Case { scrutinee; branches } ->
      let scrutinee' = apply_substitution_expression substitution scrutinee
      and branches' =
        List.map
          (fun (identifier, body) ->
            let body' = apply_substitution_expression substitution body in
            (identifier, body'))
          branches
      in
      Syntax_constructors.make_expression_case ~scrutinee:scrutinee'
        ~branches:branches'
  | Expression.Rec { identifier; type_; expression } ->
      let type_' = Option.map (apply_substitution_type substitution) type_ in
      let substitution' = Identifier.Map.remove identifier substitution in
      let expression' =
        apply_substitution_expression substitution' expression
      in
      Syntax_constructors.make_expression_rec ~identifier ~type_:type_'
        ~expression:expression'
  | Expression.Annotated { expression; type_ } ->
      let expression' = apply_substitution_expression substitution expression
      and type_' = apply_substitution_type substitution type_ in
      Syntax_constructors.make_expression_annotated ~expression:expression'
        ~type_:type_'
  | Expression.Closure { expression; environment } ->
      let expression_substitution = lift_expression_substitution environment in
      let substitution' =
        Identifier.Map.fold Identifier.Map.add substitution
          expression_substitution
      in
      apply_substitution_expression substitution' expression

let apply_stage_closure environment stage =
  let substitution = lift_stage_substitution environment in
  apply_substitution_stage substitution stage

let apply_type_closure environment type_ =
  let substitution = lift_type_substitution environment in
  apply_substitution_type substitution type_

let apply_expression_closure environment expression =
  let substitution = lift_expression_substitution environment in
  apply_substitution_expression substitution expression

let () =
  Printexc.register_printer (function
    | Invalid_stage_substitution { identifier; _ } ->
        Option.some
          (Format.asprintf
             "Invalid stage substitution for stage variable @[%a@]"
             Identifier.pp identifier)
    | Invalid_type_substitution { identifier; _ } ->
        Option.some
          (Format.asprintf "Invalid type substitution for type variable @[%a@]"
             Identifier.pp identifier)
    | Invalid_expression_substitution { identifier; _ } ->
        Option.some
          (Format.asprintf
             "Invalid expression substitution for expression variable @[%a@]"
             Identifier.pp identifier)
    | _ -> Option.none)
