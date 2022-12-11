open Syntax_definition

let rec is_substage s s' =
  match (s, s') with
  | s, s' when s = s' (* refl *) -> true
  | s, Stage.Successor { stage = s' } when s = s' (* hat *) -> true
  | _, Stage.Infinity (* infty *) -> true
  | Stage.Closure { stage; environment }, stage2 ->
      let stage1' = Substitution.apply_stage_closure environment stage in
      is_substage stage1' stage2
  | stage1, Stage.Closure { stage; environment } ->
      let stage2' = Substitution.apply_stage_closure environment stage in
      is_substage stage1 stage2'
  | _ -> false

let rec is_subtype t t' =
  match (t, t') with
  | t, t' when t = t' (* refl *) -> true
  | ( Type.Datatype { identifier = i1; stage = s1; arguments = as1 },
      Type.Datatype { identifier = i2; stage = s2; arguments = as2 } )
  (* data *) -> (
      try
        Identifier.equal i1 i2 && is_substage s1 s2
        && List.for_all2 is_subtype as1 as2
      with Invalid_argument _ -> false)
  | ( Type.Arrow { domain = d1; range = r1 },
      Type.Arrow { domain = d2; range = r2 } )
  (* funct *) ->
      is_subtype d2 d1 && is_subtype r1 r2
  | Type.Closure { type_; environment }, type2 ->
      let type1' = Substitution.apply_type_closure environment type_ in
      is_subtype type1' type2
  | type1, Type.Closure { type_; environment } ->
      let type2' = Substitution.apply_type_closure environment type_ in
      is_subtype type1 type2'
  | _ -> false

exception Stage_unification_error of { stage1 : stage; stage2 : stage }
exception Stage_variable_occurs of { identifier : identifier; stage : stage }
exception Type_unification_error of { type1 : type_; type2 : type_ }
exception Type_variable_occurs of { identifier : identifier; type_ : type_ }

let rec substage_unifier unifier stage1 stage2 =
  match (stage1, stage2) with
  | stage1, stage2 when stage1 = stage2 (* refl *) -> unifier
  | stage1, Stage.Successor { stage = stage2' } when stage1 = stage2' (* hat *)
    ->
      unifier
  | _stage1, Stage.Infinity (* infty *) -> unifier
  | Stage.Closure { stage; environment }, stage2 ->
      let stage1' = Substitution.apply_stage_closure environment stage in
      substage_unifier unifier stage1' stage2
  | stage1, Stage.Closure { stage; environment } ->
      let stage2' = Substitution.apply_stage_closure environment stage in
      substage_unifier unifier stage1 stage2'
  | Stage.Successor { stage = stage1' }, Stage.Successor { stage = stage2' } ->
      substage_unifier unifier stage1' stage2'
  | Stage.Variable { identifier }, stage2 -> (
      if Variables.variable_occurs_in_stage identifier stage2 then
        raise (Stage_variable_occurs { identifier; stage = stage2 })
      else
        match Identifier.Map.find_opt identifier unifier with
        | Option.None -> Identifier.Map.add identifier (`Stage stage2) unifier
        | Option.Some (`Stage stage1') ->
            substage_unifier unifier stage1' stage2
        | Option.Some _ -> assert false)
  | stage1, Stage.Variable { identifier } -> (
      if Variables.variable_occurs_in_stage identifier stage1 then
        raise (Stage_variable_occurs { identifier; stage = stage1 })
      else
        match Identifier.Map.find_opt identifier unifier with
        | Option.None -> Identifier.Map.add identifier (`Stage stage1) unifier
        | Option.Some (`Stage stage2') ->
            substage_unifier unifier stage1 stage2'
        | Option.Some _ -> assert false)
  | _ -> raise (Stage_unification_error { stage1; stage2 })

let rec subtype_unifier unifier type1 type2 =
  match (type1, type2) with
  | type1, type2 when type1 = type2 (* refl *) -> unifier
  | ( Type.Arrow { domain = d1; range = r1 },
      Type.Arrow { domain = d2; range = r2 } )
  (* func *) ->
      let unifier' = subtype_unifier unifier d2 d1 in
      subtype_unifier unifier' r1 r2
  | ( Type.Datatype { identifier = i1; stage = s1; arguments = as1 },
      Type.Datatype { identifier = i2; stage = s2; arguments = as2 } ) ->
      if Identifier.equal i1 i2 then
        let unifier' = substage_unifier unifier s1 s2 in
        try
          List.fold_left2
            (fun unifier a1 a2 -> subtype_unifier unifier a1 a2)
            unifier' as1 as2
        with Invalid_argument _ ->
          raise (Type_unification_error { type1; type2 })
      else raise (Type_unification_error { type1; type2 })
  | Type.Closure { type_; environment }, type2 ->
      let type1' = Substitution.apply_type_closure environment type_ in
      subtype_unifier unifier type1' type2
  | type1, Type.Closure { type_; environment } ->
      let type2' = Substitution.apply_type_closure environment type_ in
      subtype_unifier unifier type1 type2'
  | Type.Variable { identifier = i1 }, Type.Variable { identifier = i2 }
    when Identifier.equal i1 i2 ->
      unifier
  | Type.Variable { identifier }, type2 -> (
      if Variables.variable_occurs_in_type identifier type2 then
        raise (Type_variable_occurs { identifier; type_ = type2 })
      else
        match Identifier.Map.find_opt identifier unifier with
        | Option.None -> Identifier.Map.add identifier (`Type type2) unifier
        | Option.Some (`Type type1') -> subtype_unifier unifier type1' type2
        | Option.Some _ -> assert false)
  | type1, Type.Variable { identifier } -> (
      if Variables.variable_occurs_in_type identifier type1 then
        raise (Type_variable_occurs { identifier; type_ = type1 })
      else
        match Identifier.Map.find_opt identifier unifier with
        | Option.None -> Identifier.Map.add identifier (`Type type1) unifier
        | Option.Some (`Type type2') -> subtype_unifier unifier type1 type2'
        | Option.Some _ -> assert false)
  | _ -> raise (Type_unification_error { type1; type2 })

let substage_unifier = substage_unifier Identifier.Map.empty
let subtype_unifier = subtype_unifier Identifier.Map.empty

exception Expected_datatype_type

let rec get_constructor_type_datatype constructor_type =
  match constructor_type with
  | Type.Variable _ -> raise Expected_datatype_type
  | Type.Arrow { range; _ } -> get_constructor_type_datatype range
  | Type.Datatype { identifier; _ } -> identifier
  | Type.Closure { type_; environment } ->
      get_constructor_type_datatype
        (Substitution.apply_type_closure environment type_)

let rec get_arrow_type_inputs type_ =
  match type_ with
  | Type.Closure { type_; environment } ->
      get_arrow_type_inputs (Substitution.apply_type_closure environment type_)
  | Type.Arrow { domain; range } -> domain :: get_arrow_type_inputs range
  | Type.Datatype _ | Type.Variable _ -> []

let rec guard_arrow_type type_ =
  match type_ with
  | Type.Closure { type_; environment } ->
      guard_arrow_type (Substitution.apply_type_closure environment type_)
  | Type.Arrow { domain; range } -> Option.some (domain, range)
  | Type.Datatype _ | Type.Variable _ -> Option.none

exception
  Arity_mismatch of { parameters : identifier List.t; arguments : type_ List.t }

let rec replace_all_datatype_occurrences substitute type_ =
  match type_ with
  | Type.Variable _ -> type_
  | Type.Closure { type_; environment } ->
      replace_all_datatype_occurrences substitute
        (Substitution.apply_type_closure environment type_)
  | Type.Arrow { domain; range } ->
      let domain' = replace_all_datatype_occurrences substitute domain
      and range' = replace_all_datatype_occurrences substitute range in
      Syntax_constructors.make_type_arrow ~domain:domain' ~range:range'
  | Type.Datatype { identifier; stage; arguments } ->
      let arguments' =
        List.map (replace_all_datatype_occurrences substitute) arguments
      in
      Syntax_constructors.make_type_datatype ~identifier ~stage
        ~arguments:arguments'

let instantiate_constructor_type signature constructor_identifier stage
    arguments output_type =
  let _, constructor_type =
    Signature_helpers.lookup_constructor signature constructor_identifier
  in
  let datatype_identifier = get_constructor_type_datatype constructor_type in
  let _, parameters, _ =
    Signature_helpers.lookup_datatype signature datatype_identifier
  in
  let constructor_argument_types = get_arrow_type_inputs constructor_type in
  let datatype_substitute =
    Syntax_constructors.make_type_datatype ~identifier:datatype_identifier
      ~stage ~arguments
  in
  let type_ =
    List.fold_right
      (fun argument_type accumulator ->
        let domain =
          replace_all_datatype_occurrences datatype_substitute argument_type
        in
        Syntax_constructors.make_type_arrow ~domain ~range:accumulator)
      constructor_argument_types output_type
  in
  let substitution =
    List.fold_left2
      (fun substitution parameter argument ->
        Identifier.Map.add parameter argument substitution)
      Identifier.Map.empty parameters arguments
  in
  Substitution.apply_substitution_type
    (Substitution.lift_type_substitution substitution)
    type_

module Fresh_variable_state = struct
  type t = { variables_generated : Int.t }

  let[@inline] variables_generated { variables_generated; _ } =
    variables_generated

  let initial_state = { variables_generated = 0 }

  let increment_variables_generated state =
    { variables_generated = variables_generated state + 1 }

  let fresh_stage_variable state =
    let variable = "#S" ^ string_of_int (variables_generated state) in
    ( Syntax_constructors.make_stage_variable variable,
      increment_variables_generated state )

  let fresh_type_variable state =
    let variable = "#T" ^ string_of_int (variables_generated state) in
    ( Syntax_constructors.make_type_variable variable,
      increment_variables_generated state )

  let fresh_expression_variable state =
    let variable = "#E" ^ string_of_int (variables_generated state) in
    ( Syntax_constructors.make_expression_variable variable,
      increment_variables_generated state )
end

module State = struct
  type t = { signature : signature; context : type_ Identifier.Map.t }

  let[@inline] signature { signature; _ } = signature
  let[@inline] context { context; _ } = context
  let initial_state signature = { signature; context = Identifier.Map.empty }
  let[@inline] set_signature signature state = { state with signature }

  let lookup_typing state identifier =
    Identifier.Map.find_opt identifier (context state)

  let extend_typing identifier type_ state =
    { state with context = Identifier.Map.add identifier type_ state.context }

  let lookup_datatype identifier state =
    Signature_helpers.lookup_datatype (signature state) identifier

  let lookup_constructor identifier state =
    Signature_helpers.lookup_constructor (signature state) identifier
end

exception Free_variable of identifier
exception Apply_non_function of type_
exception Non_synthesizing_expression of expression
exception Type_checking_error of { expression : expression; type_ : type_ }

exception
  Type_subtyping_error of {
    expression : expression;
    subtype : type_;
    suptype : type_;
  }

exception Unsupported_untyped_recursive_expression of expression
exception Inexhaustive_case_analysis

exception
  Stage_variable_positivity_fail of {
    stage_variable : identifier;
    type_ : type_;
  }

exception
  Illegal_recursive_expression_type of {
    expression : expression;
    type_ : type_;
  }

let rec infer variables_state inference_state expression =
  match expression with
  | Expression.Variable { identifier } -> (
      match State.lookup_typing inference_state identifier with
      | Option.None -> raise (Free_variable identifier)
      | Option.Some type_ -> (variables_state, type_))
  | Expression.Constructor { identifier = constructor_identifier } ->
      let _, constructor_type =
        State.lookup_constructor constructor_identifier inference_state
      in
      let datatype_identifier =
        get_constructor_type_datatype constructor_type
      in
      let _, parameters, _ =
        State.lookup_datatype datatype_identifier inference_state
      in
      let stage, variables_state' =
        Fresh_variable_state.fresh_stage_variable variables_state
      in
      let arguments, variables_state'' =
        List.fold_left
          (fun (arguments, variables_state) _ ->
            let argument, variables_state' =
              Fresh_variable_state.fresh_type_variable variables_state
            in
            (argument :: arguments, variables_state'))
          ([], variables_state') parameters
      in
      let output_type =
        Type.Datatype
          {
            identifier = datatype_identifier;
            stage = Stage.Successor { stage };
            arguments;
          }
      in
      let instantiated_type =
        instantiate_constructor_type
          (State.signature inference_state)
          constructor_identifier stage arguments output_type
      in
      (variables_state'', instantiated_type)
  | Expression.Application { applicand; argument } -> (
      match infer variables_state inference_state applicand with
      | variables_state', Type.Arrow { domain; range } ->
          let variables_state'' =
            check variables_state' inference_state argument domain
          in
          (variables_state'', range)
      | _, applicand_type -> raise (Apply_non_function applicand_type))
  | Expression.Rec { identifier; type_; expression = inner_expression } -> (
      match type_ with
      | Option.Some type_ ->
          let datatype_identifier, stage_variable, arguments, range =
            match guard_arrow_type type_ with
            | Option.Some
                ( Type.Datatype
                    {
                      identifier = datatype_identifier;
                      stage = Stage.Variable { identifier = stage_variable };
                      arguments;
                    },
                  range ) ->
                (datatype_identifier, stage_variable, arguments, range)
            | Option.Some _ | Option.None ->
                raise (Illegal_recursive_expression_type { expression; type_ })
          in
          if
            Variables.stage_variable_is_positive_with_respect_to range
              stage_variable
          then
            let stage_hat =
              Syntax_constructors.make_stage_successor
                (Syntax_constructors.make_stage_variable stage_variable)
            in
            let domain' =
              Syntax_constructors.make_type_datatype
                ~identifier:datatype_identifier ~stage:stage_hat ~arguments
            in
            let range' =
              Substitution.apply_substitution_type
                (Identifier.Map.singleton stage_variable (`Stage stage_hat))
                range
            in
            let type_to_check =
              Syntax_constructors.make_type_arrow ~domain:domain' ~range:range'
            in
            let inference_state' =
              State.extend_typing identifier type_ inference_state
            in
            let variables_state' =
              check variables_state inference_state' inner_expression
                type_to_check
            in
            let stage_s, variables_state'' =
              Fresh_variable_state.fresh_stage_variable variables_state'
            in
            let domain'' =
              Syntax_constructors.make_type_datatype
                ~identifier:datatype_identifier ~stage:stage_s ~arguments
            in
            let range'' =
              Substitution.apply_substitution_type
                (Identifier.Map.singleton stage_variable (`Stage stage_s))
                range
            in
            let inferred_type =
              Syntax_constructors.make_type_arrow ~domain:domain''
                ~range:range''
            in
            (variables_state'', inferred_type)
          else
            raise
              (Stage_variable_positivity_fail { stage_variable; type_ = range })
      | Option.None ->
          raise (Unsupported_untyped_recursive_expression expression))
  | Expression.Annotated { expression; type_ } ->
      let variables_state' =
        check variables_state inference_state expression type_
      in
      (variables_state', type_)
  | Expression.Abstraction _ | Expression.Case _ ->
      raise (Non_synthesizing_expression expression)
  | Expression.Closure { expression; environment } ->
      infer variables_state inference_state
        (Substitution.apply_expression_closure environment expression)

and check variables_state inference_state expression type_ =
  match expression with
  | Expression.Abstraction { parameter_identifier; parameter_type; body } -> (
      match type_ with
      | Type.Arrow { domain; range } -> (
          match parameter_type with
          | Option.Some parameter_type ->
              ignore (subtype_unifier domain parameter_type);
              let inference_state' =
                State.extend_typing parameter_identifier domain inference_state
              in
              check variables_state inference_state' body range
          | Option.None ->
              let inference_state' =
                State.extend_typing parameter_identifier domain inference_state
              in
              check variables_state inference_state' body range)
      | _ -> raise (Type_checking_error { expression; type_ }))
  | Expression.Case { scrutinee; branches } -> (
      match infer variables_state inference_state scrutinee with
      | ( variables_state',
          Type.Datatype
            {
              identifier = datatype_identifier;
              stage = Stage.Successor { stage };
              arguments;
            } ) ->
          let _, _, constructor_declarations =
            State.lookup_datatype datatype_identifier inference_state
          in
          List.fold_left
            (fun variables_state constructor_declaration ->
              match constructor_declaration with
              | Declaration.Constructor
                  { identifier = constructor_identifier; _ } -> (
                  match
                    List.find_map
                      (fun (constructor_identifier', body) ->
                        if
                          Identifier.equal constructor_identifier
                            constructor_identifier'
                        then Option.some body
                        else Option.none)
                      branches
                  with
                  | Option.None -> raise Inexhaustive_case_analysis
                  | Option.Some body ->
                      let expected_type =
                        instantiate_constructor_type
                          (State.signature inference_state)
                          constructor_identifier stage arguments type_
                      in
                      check variables_state inference_state body expected_type)
              | _ ->
                  raise
                    (Malformed_declaration
                       (Signature_helpers.lookup_signature
                          (State.signature inference_state)
                          datatype_identifier)))
            variables_state' constructor_declarations
      | _ -> raise (Type_checking_error { expression; type_ }))
  | Expression.Constructor _ | Expression.Rec _ | Expression.Application _
  | Expression.Annotated _ | Expression.Variable _ -> (
      let variables_state', tau =
        infer variables_state inference_state expression
      in
      try
        let unifier = subtype_unifier tau type_ in
        assert (
          is_subtype
            (Substitution.apply_substitution_type unifier tau)
            (Substitution.apply_substitution_type unifier type_));
        variables_state'
      with _ ->
        raise
          (Type_subtyping_error { expression; subtype = tau; suptype = type_ }))
  | Expression.Closure { expression; environment } ->
      check variables_state inference_state
        (Substitution.apply_expression_closure environment expression)
        type_

let () =
  Printexc.register_printer (function
    | Stage_unification_error { stage1; stage2 } ->
        Option.some
          (Format.asprintf "The unification of stages @[%a@] and @[%a@] failed"
             Syntax_pp.pp_stage stage1 Syntax_pp.pp_stage stage2)
    | Stage_variable_occurs { stage; identifier } ->
        Option.some
          (Format.asprintf
             "Occurs check failed for variable @[%a@] in stage @[%a@]"
             Identifier.pp identifier Syntax_pp.pp_stage stage)
    | Type_unification_error { type1; type2 } ->
        Option.some
          (Format.asprintf "The unification of types @[%a@] and @[%a@] failed"
             Syntax_pp.pp_type type1 Syntax_pp.pp_type type2)
    | Type_variable_occurs { type_; identifier } ->
        Option.some
          (Format.asprintf
             "Occurs check failed for variable @[%a@] in type @[%a@]"
             Identifier.pp identifier Syntax_pp.pp_type type_)
    | Expected_datatype_type ->
        Option.some
          (Format.asprintf
             "Expected the head type of a constructor to be a datatype")
    | Arity_mismatch _ ->
        Option.some
          (Format.asprintf
             "Arity mismatch between parameters and arguments to a datatype")
    | Free_variable identifier ->
        Option.some
          (Format.asprintf
             "Free variable @[%a@] encountered during type inference"
             Identifier.pp identifier)
    | Apply_non_function type_ ->
        Option.some
          (Format.asprintf
             "Invalid application of an expression having type @[%a@]"
             Syntax_pp.pp_type type_)
    | Non_synthesizing_expression expression ->
        Option.some
          (Format.asprintf "Expression @[%a@] does not synthesize a type"
             Syntax_pp.pp_expression expression)
    | Type_checking_error { expression; type_ } ->
        Option.some
          (Format.asprintf
             "The expression @[%a@] does not check against the type @[%a@]"
             Syntax_pp.pp_expression expression Syntax_pp.pp_type type_)
    | Type_subtyping_error { expression; subtype; suptype } ->
        Option.some
          (Format.asprintf
             "The expression @[%a@] having inferred type @[%a@] is not a \
              subtype of @[%a@]"
             Syntax_pp.pp_expression expression Syntax_pp.pp_type subtype
             Syntax_pp.pp_type suptype)
    | Unsupported_untyped_recursive_expression expression ->
        Option.some
          (Format.asprintf
             "Unsupported type inference for untyped recursive expression \
              @[%a@]"
             Syntax_pp.pp_expression expression)
    | Inexhaustive_case_analysis ->
        Option.some
          (Format.asprintf
             "Encountered an inexhaustive case analysis during type-checking")
    | Stage_variable_positivity_fail { stage_variable; type_ } ->
        Option.some
          (Format.asprintf
             "Positivity check failed for stage variable @[%a@] in type @[%a@]"
             Identifier.pp stage_variable Syntax_pp.pp_type type_)
    | Illegal_recursive_expression_type { expression; type_ } ->
        Option.some
          (Format.asprintf "Illegal type @[%a@] for recursive expression @[%a@]"
             Syntax_pp.pp_type type_ Syntax_pp.pp_expression expression)
    | _ -> Option.none)
