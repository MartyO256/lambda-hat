open Syntax

let rec variable_occurs_in_stage variable stage =
  match stage with
  | Stage.Existential_variable { identifier } | Stage.Variable { identifier } ->
      Identifier.equal variable identifier
  | Stage.Successor { stage } -> variable_occurs_in_stage variable stage
  | Stage.Infinity -> false
  | Stage.Closure { stage; environment } ->
      variable_occurs_in_stage variable
        (Substitution.apply_stage_closure environment stage)

let variable_does_not_occur_in_stage variable stage =
  Bool.not (variable_occurs_in_stage variable stage)

let rec variable_occurs_in_type variable type_ =
  match type_ with
  | Type.Existential_variable { identifier } | Type.Variable { identifier } ->
      Identifier.equal variable identifier
  | Type.Arrow { domain; range } ->
      variable_occurs_in_type variable domain
      || variable_occurs_in_type variable range
  | Type.Datatype { stage; arguments; _ } ->
      variable_occurs_in_stage variable stage
      || List.exists
           (fun type_ -> variable_occurs_in_type variable type_)
           arguments
  | Type.Closure { type_; environment } ->
      variable_occurs_in_type variable
        (Substitution.apply_type_closure environment type_)

let variable_does_not_occur_in_type variable type_ =
  Bool.not (variable_occurs_in_type variable type_)

let rec stage_variable_is_positive_with_respect_to type_ variable =
  match type_ with
  | Type.Existential_variable _ | Type.Variable _ -> true
  | Type.Arrow { domain; range } ->
      stage_variable_is_negative_with_respect_to domain variable
      && stage_variable_is_positive_with_respect_to range variable
  | Type.Datatype { arguments; _ } ->
      List.for_all
        (fun type_ -> stage_variable_is_positive_with_respect_to type_ variable)
        arguments
  | Type.Closure { type_; environment } ->
      stage_variable_is_positive_with_respect_to
        (Substitution.apply_type_closure environment type_)
        variable

and stage_variable_is_negative_with_respect_to type_ variable =
  match type_ with
  | Type.Existential_variable _ | Type.Variable _ -> true
  | Type.Arrow { domain; range } ->
      stage_variable_is_positive_with_respect_to domain variable
      && stage_variable_is_negative_with_respect_to range variable
  | Type.Datatype { stage; arguments; _ } ->
      variable_does_not_occur_in_stage variable stage
      && List.for_all
           (fun type_ ->
             stage_variable_is_negative_with_respect_to type_ variable)
           arguments
  | Type.Closure { type_; environment } ->
      stage_variable_is_negative_with_respect_to
        (Substitution.apply_type_closure environment type_)
        variable

and type_variable_is_positive_with_respect_to type_ variable =
  match type_ with
  | Type.Existential_variable _ | Type.Variable _ -> true
  | Type.Arrow { domain; range } ->
      type_variable_is_negative_with_respect_to domain variable
      && type_variable_is_positive_with_respect_to range variable
  | Type.Datatype { arguments; _ } ->
      List.for_all
        (fun type_ -> type_variable_is_positive_with_respect_to type_ variable)
        arguments
  | Type.Closure { type_; environment } ->
      type_variable_is_positive_with_respect_to
        (Substitution.apply_type_closure environment type_)
        variable

and type_variable_is_negative_with_respect_to type_ variable =
  match type_ with
  | Type.Existential_variable { identifier } | Type.Variable { identifier } ->
      Bool.not (Identifier.equal variable identifier)
  | Type.Arrow { domain; range } ->
      type_variable_is_positive_with_respect_to domain variable
      && type_variable_is_negative_with_respect_to range variable
  | Type.Datatype { arguments; _ } ->
      List.for_all
        (fun type_ -> type_variable_is_negative_with_respect_to type_ variable)
        arguments
  | Type.Closure { type_; environment } ->
      type_variable_is_negative_with_respect_to
        (Substitution.apply_type_closure environment type_)
        variable

and datatype_is_positive_with_respect_to type_ datatype =
  match type_ with
  | Type.Existential_variable _ | Type.Variable _ -> true
  | Type.Arrow { domain; range } ->
      datatype_is_negative_with_respect_to domain datatype
      && datatype_is_positive_with_respect_to range datatype
  | Type.Datatype { arguments; _ } ->
      List.for_all
        (fun type_ -> datatype_is_positive_with_respect_to type_ datatype)
        arguments
  | Type.Closure { type_; environment } ->
      datatype_is_positive_with_respect_to
        (Substitution.apply_type_closure environment type_)
        datatype

and datatype_is_negative_with_respect_to type_ datatype =
  match type_ with
  | Type.Existential_variable { identifier } | Type.Variable { identifier } ->
      Bool.not (Identifier.equal datatype identifier)
  | Type.Arrow { domain; range } ->
      datatype_is_positive_with_respect_to domain datatype
      && datatype_is_negative_with_respect_to range datatype
  | Type.Datatype { arguments; identifier; _ } ->
      Bool.not (Identifier.equal datatype identifier)
      || List.for_all
           (fun type_ -> datatype_is_negative_with_respect_to type_ datatype)
           arguments
  | Type.Closure { type_; environment } ->
      datatype_is_negative_with_respect_to
        (Substitution.apply_type_closure environment type_)
        datatype

let rec collect_variables_type type_ =
  match type_ with
  | Type.Existential_variable { identifier } | Type.Variable { identifier } ->
      Identifier.Set.singleton identifier
  | Type.Arrow { domain; range } ->
      Identifier.Set.union
        (collect_variables_type domain)
        (collect_variables_type range)
  | Type.Datatype { arguments; _ } ->
      List.fold_left
        (fun accumulator argument ->
          Identifier.Set.union (collect_variables_type argument) accumulator)
        Identifier.Set.empty arguments
  | Type.Closure { type_; environment } ->
      collect_variables_type (Substitution.apply_type_closure environment type_)

let rec replace_type_variables_with_existential_type_variables type_ =
  match type_ with
  | Type.Existential_variable _ -> type_
  | Type.Variable { identifier } ->
      Syntax_constructors.make_type_existential_variable identifier
  | Type.Arrow { domain; range } ->
      let domain' =
        replace_type_variables_with_existential_type_variables domain
      in
      let range' =
        replace_type_variables_with_existential_type_variables range
      in
      Syntax_constructors.make_type_arrow ~domain:domain' ~range:range'
  | Type.Datatype { identifier; stage; arguments } ->
      let arguments' =
        List.map replace_type_variables_with_existential_type_variables
          arguments
      in
      Syntax_constructors.make_type_datatype ~identifier ~stage
        ~arguments:arguments'
  | Type.Closure { type_; environment } ->
      replace_type_variables_with_existential_type_variables
        (Substitution.apply_type_closure environment type_)
