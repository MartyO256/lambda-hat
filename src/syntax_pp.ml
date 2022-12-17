open Syntax_definition

let rec precedence_type type_ =
  match type_ with
  | Type.Existential_variable _ | Type.Variable _ -> 3
  | Type.Datatype _ -> 2
  | Type.Arrow _ -> 1
  | Type.Closure { type_; _ } -> precedence_type type_

let rec precedence_expression expression =
  match expression with
  | Expression.Existential_variable _ | Expression.Variable _
  | Expression.Constructor _ ->
      6
  | Expression.Application _ -> 5
  | Expression.Case _ -> 4
  | Expression.Annotated _ -> 3
  | Expression.Rec _ -> 2
  | Expression.Abstraction _ -> 1
  | Expression.Closure { expression; _ } -> precedence_expression expression

let pp_parenthesized ppf ppv v = Format.fprintf ppf "@[(%a)@]" ppv v

let rec pp_stage ppf stage =
  match stage with
  | Stage.Existential_variable { identifier } -> Identifier.pp ppf identifier
  | Stage.Variable { identifier } -> Identifier.pp ppf identifier
  | Stage.Successor { stage } -> Format.fprintf ppf "$%a" pp_stage stage
  | Stage.Infinity -> Format.pp_print_string ppf "∞"
  | Stage.Closure { stage; environment } ->
      pp_stage ppf (Substitution.apply_stage_closure environment stage)

and pp_type ppf type_ =
  match type_ with
  | Type.Existential_variable { identifier } -> Identifier.pp ppf identifier
  | Type.Variable { identifier } -> Identifier.pp ppf identifier
  | Type.Arrow { domain; range } ->
      Format.fprintf ppf "@[<2>%a@ →@ %a@]"
        (fun ppf argument ->
          if precedence_type argument <= precedence_type type_ then
            pp_parenthesized ppf pp_type argument
          else pp_type ppf argument)
        domain
        (fun ppf argument ->
          if precedence_type argument < precedence_type type_ then
            pp_parenthesized ppf pp_type argument
          else pp_type ppf argument)
        range
  | Type.Datatype { identifier; stage; arguments } -> (
      match arguments with
      | [] ->
          Format.fprintf ppf "@[%a^%a@]" Identifier.pp identifier pp_stage stage
      | _ ->
          Format.fprintf ppf "@[%a^%a@ %a@]" Identifier.pp identifier pp_stage
            stage
            (Format.pp_print_list
               ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
               (fun ppf argument ->
                 if precedence_type argument <= precedence_type type_ then
                   pp_parenthesized ppf pp_type argument
                 else pp_type ppf argument))
            arguments)
  | Type.Closure { type_; environment } ->
      pp_type ppf (Substitution.apply_type_closure environment type_)

and pp_type_without_stages ppf type_ =
  match type_ with
  | Type.Existential_variable { identifier } -> Identifier.pp ppf identifier
  | Type.Variable { identifier } -> Identifier.pp ppf identifier
  | Type.Arrow { domain; range } ->
      Format.fprintf ppf "@[<2>%a@ →@ %a@]"
        (fun ppf argument ->
          if precedence_type argument <= precedence_type type_ then
            pp_parenthesized ppf pp_type argument
          else pp_type ppf argument)
        domain
        (fun ppf argument ->
          if precedence_type argument < precedence_type type_ then
            pp_parenthesized ppf pp_type argument
          else pp_type ppf argument)
        range
  | Type.Datatype { identifier; arguments; _ } -> (
      match arguments with
      | [] -> Identifier.pp ppf identifier
      | _ ->
          Format.fprintf ppf "@[%a@ %a@]" Identifier.pp identifier
            (Format.pp_print_list
               ~pp_sep:(fun ppf () -> Format.fprintf ppf "@ ")
               (fun ppf argument ->
                 if precedence_type argument <= precedence_type type_ then
                   pp_parenthesized ppf pp_type argument
                 else pp_type ppf argument))
            arguments)
  | Type.Closure { type_; environment } ->
      pp_type ppf (Substitution.apply_type_closure environment type_)

and pp_expression ppf expression =
  match expression with
  | Expression.Existential_variable { identifier } ->
      Identifier.pp ppf identifier
  | Expression.Variable { identifier } -> Identifier.pp ppf identifier
  | Expression.Constructor { identifier } -> Identifier.pp ppf identifier
  | Expression.Abstraction { parameter_identifier; parameter_type; body } -> (
      match parameter_type with
      | Option.None ->
          Format.fprintf ppf "λ%a.@ %a" Identifier.pp parameter_identifier
            pp_expression body
      | Option.Some parameter_type ->
          Format.fprintf ppf "λ%a :@ %a.@ %a" Identifier.pp parameter_identifier
            pp_type parameter_type pp_expression body)
  | Expression.Case { scrutinee; branches } -> (
      match branches with
      | [] -> raise (Malformed_expression expression)
      | [ branch ] ->
          Format.fprintf ppf "@[<v 2>case @[<2>%a@] of @<20>{@ %a@]@;}"
            (fun ppf scrutinee ->
              if
                precedence_expression scrutinee
                <= precedence_expression expression
              then pp_parenthesized ppf pp_expression scrutinee
              else pp_expression ppf scrutinee)
            scrutinee
            (fun ppf (constructor, body) ->
              Format.fprintf ppf "@[<2>%a ⇒@;%a@]" Identifier.pp constructor
                pp_expression body)
            branch
      | branches ->
          Format.fprintf ppf "@[<v 2>case @[<2>%a@] of @<20>{@;| %a@]@;}"
            (fun ppf scrutinee ->
              if
                precedence_expression scrutinee
                <= precedence_expression expression
              then pp_parenthesized ppf pp_expression scrutinee
              else pp_expression ppf scrutinee)
            scrutinee
            (Format.pp_print_list
               ~pp_sep:(fun ppf () -> Format.fprintf ppf "@;| ")
               (fun ppf (constructor, body) ->
                 Format.fprintf ppf "@[<2>%a ⇒@;%a@]" Identifier.pp constructor
                   pp_expression body))
            branches)
  | Expression.Rec { identifier; type_; expression } -> (
      match type_ with
      | Option.None ->
          Format.fprintf ppf "letrec@ %a =@;%a" Identifier.pp identifier
            pp_expression expression
      | Option.Some type_ ->
          Format.fprintf ppf "letrec@ %a :@ %a =@;%a" Identifier.pp identifier
            pp_type type_ pp_expression expression)
  | Expression.Application { applicand; argument } ->
      Format.fprintf ppf "%a@ %a"
        (fun ppf applicand ->
          if precedence_expression applicand < precedence_expression expression
          then pp_parenthesized ppf pp_expression applicand
          else pp_expression ppf applicand)
        applicand
        (fun ppf argument ->
          if precedence_expression argument <= precedence_expression expression
          then pp_parenthesized ppf pp_expression argument
          else pp_expression ppf argument)
        argument
  | Expression.Annotated { expression = annotated; type_ } ->
      Format.fprintf ppf "%a :@ %a"
        (fun ppf annotated ->
          if precedence_expression annotated <= precedence_expression expression
          then pp_parenthesized ppf pp_expression annotated
          else pp_expression ppf annotated)
        annotated pp_type type_
  | Expression.Closure { expression; environment } ->
      pp_expression ppf
        (Substitution.apply_expression_closure environment expression)

and pp_declaration ppf declaration =
  match declaration with
  | Declaration.Constructor { identifier; type_ } ->
      Format.fprintf ppf "@[<2>%a :@ %a@]" Identifier.pp identifier
        pp_type_without_stages type_
  | Declaration.Datatype { identifier; parameters; constructors } -> (
      match parameters with
      | [] ->
          Format.fprintf ppf "@[<v 2>datatype %a =@;| %a@]" Identifier.pp
            identifier
            (Format.pp_print_list
               ~pp_sep:(fun ppf () -> Format.fprintf ppf "@;| ")
               pp_declaration)
            constructors
      | parameters ->
          Format.fprintf ppf "@[<v 2>datatype %a %a =@;| %a@]" Identifier.pp
            identifier
            (Format.pp_print_list
               ~pp_sep:(fun ppf () -> Format.fprintf ppf " ")
               Identifier.pp)
            parameters
            (Format.pp_print_list
               ~pp_sep:(fun ppf () -> Format.fprintf ppf "@;| ")
               pp_declaration)
            constructors)
  | Declaration.Value { identifier; expression } ->
      Format.fprintf ppf "@[<2>let@ %a =@;%a@]" Identifier.pp identifier
        pp_expression expression

and pp_signature ppf signature =
  let { Signature.declarations_rev; _ } = signature in
  Format.fprintf ppf "@[<v 0>%a@]"
    (Format.pp_print_list
       ~pp_sep:(fun ppf () -> Format.fprintf ppf "@;@;")
       pp_declaration)
    (List.rev (List.map (fun (_, declaration) -> declaration) declarations_rev))
