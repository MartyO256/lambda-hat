open Syntax_definition

let rec get_arrow_type_inputs type_ =
  match type_ with
  | Type.Closure { type_; environment } ->
      get_arrow_type_inputs (Substitution.apply_type_closure environment type_)
  | Type.Arrow { domain; range } -> domain :: get_arrow_type_inputs range
  | Type.Datatype _ | Type.Existential_variable _ | Type.Variable _ -> []

exception Illegal_existential_stage_variable of identifier
exception Illegal_existential_type_variable of identifier
exception Illegal_existential_expression_variable of identifier

let rec validate_stage _signature stage =
  match stage with
  | Stage.Existential_variable { identifier } ->
      raise (Illegal_existential_stage_variable identifier)
  | _ -> ()

and validate_type signature type_ =
  match type_ with
  | Type.Existential_variable { identifier } ->
      raise (Illegal_existential_type_variable identifier)
  | Type.Variable _ -> ()
  | Type.Arrow { domain; range } ->
      validate_type signature domain;
      validate_type signature range
  | Type.Datatype { identifier; stage; arguments } ->
      ignore (Signature_helpers.lookup_datatype signature identifier);
      validate_stage signature stage;
      List.iter (validate_type signature) arguments
  | Type.Closure { type_; environment } ->
      validate_type signature
        (Substitution.apply_type_closure environment type_)

and validate_expression signature expression =
  match expression with
  | Expression.Existential_variable { identifier } ->
      raise (Illegal_existential_expression_variable identifier)
  | Expression.Variable _ -> ()
  | Expression.Constructor { identifier } ->
      ignore (Signature_helpers.lookup_constructor signature identifier)
  | Expression.Abstraction { parameter_type; body; _ } ->
      (match parameter_type with
      | Option.Some parameter_type -> validate_type signature parameter_type
      | Option.None -> ());
      validate_expression signature body
  | Expression.Application { applicand; argument } ->
      validate_expression signature applicand;
      validate_expression signature argument
  | Expression.Case { scrutinee; branches } ->
      validate_expression signature scrutinee;
      List.iter
        (fun (constructor_identifier, body) ->
          ignore
            (Signature_helpers.lookup_constructor signature
               constructor_identifier);
          validate_expression signature body)
        branches
  | Expression.Rec { type_; expression; _ } ->
      (match type_ with
      | Option.Some type_ -> validate_type signature type_
      | Option.None -> ());
      validate_expression signature expression
  | Expression.Annotated { expression; type_ } ->
      validate_expression signature expression;
      validate_type signature type_
  | Expression.Closure { expression; environment } ->
      validate_expression signature
        (Substitution.apply_expression_closure environment expression)

exception Duplicate_datatype_parameters of identifier List.t
exception Invalid_constructor_declaration

let validate_datatype_parameters parameters =
  match Identifier.find_duplicates parameters with
  | Option.None -> ()
  | Option.Some duplicates -> raise (Duplicate_datatype_parameters duplicates)

let rec validate_constructor_end_type datatype_identifier datatype_parameters
    type_ =
  match type_ with
  | Type.Existential_variable _ | Type.Variable _ ->
      raise Invalid_constructor_declaration
  | Type.Arrow { range; _ } ->
      validate_constructor_end_type datatype_identifier datatype_parameters
        range
  | Type.Datatype { identifier = identifier'; arguments; _ } -> (
      if Identifier.equal datatype_identifier identifier' then ()
      else raise Invalid_constructor_declaration;
      try
        List.iter2
          (fun parameter argument ->
            match argument with
            | Type.Variable { identifier } ->
                if Identifier.equal parameter identifier then ()
                else raise Invalid_constructor_declaration
            | _ -> raise Invalid_constructor_declaration)
          datatype_parameters arguments
      with Invalid_argument _ -> raise Invalid_constructor_declaration)
  | Type.Closure { type_; environment } ->
      validate_constructor_end_type datatype_identifier datatype_parameters
        (Substitution.apply_type_closure environment type_)

exception Constructor_scheme_positivity_fail

let validate_constructor_scheme_positivity constructor_input_types
    datatype_identifier datatype_parameters =
  if
    List.for_all
      (fun input_type ->
        Variables.datatype_is_positive_with_respect_to input_type
          datatype_identifier)
      constructor_input_types
    && List.for_all
         (fun datatype_parameter ->
           List.for_all
             (fun input_type ->
               Variables.type_variable_is_positive_with_respect_to input_type
                 datatype_parameter)
             constructor_input_types)
         datatype_parameters
  then ()
  else raise Constructor_scheme_positivity_fail

exception Invalid_type_variables

let validate_declaration signature declaration =
  match declaration with
  | Declaration.Constructor { type_; _ } -> validate_type signature type_
  | Declaration.Datatype { identifier; parameters; constructors } ->
      validate_datatype_parameters parameters;
      List.iter
        (fun constructor_declaration ->
          match constructor_declaration with
          | Declaration.Constructor { type_; _ } ->
              validate_constructor_end_type identifier parameters type_;
              let inputs = get_arrow_type_inputs type_ in
              validate_constructor_scheme_positivity inputs identifier
                parameters;
              validate_type signature type_;
              let type_variables =
                List.fold_left
                  (fun accumulator input ->
                    Identifier.Set.union
                      (Variables.collect_variables_type input)
                      accumulator)
                  Identifier.Set.empty inputs
              in
              let parameters_set = Identifier.Set.of_list parameters in
              if Identifier.Set.subset type_variables parameters_set then ()
              else raise Invalid_type_variables
          | _ -> raise (Malformed_declaration declaration))
        constructors
  | Declaration.Value { expression; _ } ->
      validate_expression signature expression

let validate_signature signature =
  let { Signature.declarations_rev; _ } = signature in
  let declarations = List.rev declarations_rev in
  List.iter
    (fun (signature_lazy, declaration) ->
      let signature = Lazy.force signature_lazy in
      validate_declaration signature declaration)
    declarations

let () =
  Printexc.register_printer (function
    | Illegal_existential_stage_variable identifier ->
        Option.some
          (Format.asprintf "Illegal existential stage variable@ %a"
             Identifier.pp identifier)
    | Illegal_existential_type_variable identifier ->
        Option.some
          (Format.asprintf "Illegal existential type variable@ %a" Identifier.pp
             identifier)
    | Illegal_existential_expression_variable identifier ->
        Option.some
          (Format.asprintf "Illegal existential expression variable@ %a"
             Identifier.pp identifier)
    | Duplicate_datatype_parameters parameters ->
        Option.some
          (Format.asprintf "Duplicate datatype parameters@ %a"
             (Format.pp_print_list
                ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
                Identifier.pp)
             parameters)
    | Invalid_constructor_declaration ->
        Option.some
          (Format.asprintf "Encountered an invalid constructor declaration")
    | Constructor_scheme_positivity_fail ->
        Option.some (Format.asprintf "Constructor scheme positivity failed")
    | Invalid_type_variables ->
        Option.some
          (Format.asprintf "Constructor scheme type variables check failed")
    | _ -> Option.none)
