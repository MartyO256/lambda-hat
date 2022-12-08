open Syntax_definition

let[@inline] json_of_association e = `Assoc e
let[@inline] json_of_int i = `Int i
let[@inline] json_of_bool b = `Bool b
let[@inline] json_of_string s = `String s
let[@inline] json_of_list f l = `List (List.map f l)

let[@inline] json_of_variant ~name ~data =
  `List [ json_of_string name; json_of_association data ]

let[@inline] json_of_option v o =
  match o with Option.Some x -> v x | Option.None -> `Null

let json_of_identifier = json_of_string

let rec json_of_stage stage =
  match stage with
  | Stage.Variable { identifier } ->
      json_of_variant ~name:"Stage.Variable"
        ~data:[ ("identifier", json_of_identifier identifier) ]
  | Stage.Successor { stage } ->
      json_of_variant ~name:"Stage.Successor"
        ~data:[ ("stage", json_of_stage stage) ]
  | Stage.Infinity -> json_of_variant ~name:"Stage.Infinity" ~data:[]
  | Stage.Closure { stage; environment } ->
      json_of_stage (Substitution.apply_stage_closure environment stage)

and json_of_type type_ =
  match type_ with
  | Type.Variable { identifier } ->
      json_of_variant ~name:"Type.Variable"
        ~data:[ ("identifier", json_of_identifier identifier) ]
  | Type.Arrow { domain; range } ->
      json_of_variant ~name:"Type.Arrow"
        ~data:[ ("domain", json_of_type domain); ("range", json_of_type range) ]
  | Type.Datatype { identifier; stage; arguments } ->
      json_of_variant ~name:"Type.Datatype"
        ~data:
          [
            ("identifier", json_of_identifier identifier);
            ("stage", json_of_stage stage);
            ("arguments", json_of_list json_of_type arguments);
          ]
  | Type.Closure { type_; environment } ->
      json_of_type (Substitution.apply_type_closure environment type_)

and json_of_expression expression =
  match expression with
  | Expression.Variable { identifier } ->
      json_of_variant ~name:"Expression.Variable"
        ~data:[ ("identifier", json_of_identifier identifier) ]
  | Expression.Constructor { identifier } ->
      json_of_variant ~name:"Expression.Constructor"
        ~data:[ ("identifier", json_of_identifier identifier) ]
  | Expression.Abstraction { parameter_identifier; parameter_type; body } ->
      json_of_variant ~name:"Expression.Abstraction"
        ~data:
          [
            ("parameter_identifier", json_of_identifier parameter_identifier);
            ("parameter_type", json_of_option json_of_type parameter_type);
            ("body", json_of_expression body);
          ]
  | Expression.Application { applicand; argument } ->
      json_of_variant ~name:"Expression.Application"
        ~data:
          [
            ("applicand", json_of_expression applicand);
            ("argument", json_of_expression argument);
          ]
  | Expression.Case { scrutinee; branches } ->
      let json_of_branch branch =
        let identifier, body = branch in
        `List [ json_of_identifier identifier; json_of_expression body ]
      in
      json_of_variant ~name:"Expression.Case"
        ~data:
          [
            ("scrutinee", json_of_expression scrutinee);
            ("branches", json_of_list json_of_branch branches);
          ]
  | Expression.Rec { identifier; type_; expression } ->
      json_of_variant ~name:"Expression.Rec"
        ~data:
          [
            ("identifier", json_of_identifier identifier);
            ("type_", json_of_option json_of_type type_);
            ("expression", json_of_expression expression);
          ]
  | Expression.Annotated { expression; type_ } ->
      json_of_variant ~name:"Expression.Annotated"
        ~data:
          [
            ("expression", json_of_expression expression);
            ("type_", json_of_type type_);
          ]
  | Expression.Closure { expression; environment } ->
      json_of_expression
        (Substitution.apply_expression_closure environment expression)

and json_of_declaration declaration =
  match declaration with
  | Declaration.Constructor { identifier; type_ } ->
      json_of_variant ~name:"Declaration.Datatype"
        ~data:
          [
            ("identifier", json_of_identifier identifier);
            ("type", json_of_type type_);
          ]
  | Declaration.Datatype { identifier; parameters; constructors } ->
      json_of_variant ~name:"Declaration.Datatype"
        ~data:
          [
            ("identifier", json_of_identifier identifier);
            ("parameters", json_of_list json_of_identifier parameters);
            ( "constructors",
              json_of_list
                (json_of_declaration : declaration -> Yojson.Safe.t)
                constructors );
          ]
  | Declaration.Value { identifier; expression } ->
      json_of_variant ~name:"Declaration.Value"
        ~data:
          [
            ("identifier", json_of_identifier identifier);
            ("expression", json_of_expression expression);
          ]

and json_of_signature signature =
  let { Signature.declarations_rev; _ } = signature in
  json_of_variant ~name:"Signature"
    ~data:
      [
        ( "declarations",
          json_of_list json_of_declaration
            (List.rev
               (List.map (fun (_, declaration) -> declaration) declarations_rev))
        );
      ]
