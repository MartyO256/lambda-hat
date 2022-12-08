open Syntax_definition

let make_stage_variable identifier = Stage.Variable { identifier }
let make_stage_successor stage = Stage.Successor { stage }
let make_stage_infinity = Stage.Infinity
let make_type_variable identifier = Type.Variable { identifier }
let make_type_arrow ~domain ~range = Type.Arrow { domain; range }

let make_type_datatype ~identifier ~stage ~arguments =
  Type.Datatype { identifier; stage; arguments }

let make_expression_variable identifier = Expression.Variable { identifier }

let make_expression_constructor identifier =
  Expression.Constructor { identifier }

let make_expression_abstraction ~parameter_identifier ~parameter_type ~body =
  Expression.Abstraction { parameter_identifier; parameter_type; body }

let make_expression_application ~applicand ~argument =
  Expression.Application { applicand; argument }

let make_expression_case ~scrutinee ~branches =
  Expression.Case { scrutinee; branches }

let make_expression_rec ~identifier ~type_ ~expression =
  Expression.Rec { identifier; type_; expression }

let make_expression_annotated ~expression ~type_ =
  Expression.Annotated { expression; type_ }

let make_expression_closure ~expression ~environment =
  Expression.Closure { expression; environment }

let make_declaration_constructor ~identifier ~type_ =
  Declaration.Constructor { identifier; type_ }

let make_declaration_datatype ~identifier ~parameters ~constructors =
  Declaration.Datatype { identifier; parameters; constructors }

let make_declaration_value ~identifier ~expression =
  Declaration.Value { identifier; expression }

exception Duplicate_identifiers of identifier List.t

let empty_signature =
  { Signature.declarations_rev = []; bindings = Identifier.Map.empty }

let add_declaration_binding declaration_bindings declaration =
  match declaration with
  | Declaration.Constructor { identifier; _ }
  | Declaration.Datatype { identifier; _ }
  | Declaration.Value { identifier; _ } ->
      (identifier, declaration) :: declaration_bindings

let add_declaration signature declaration =
  let rec signature' =
    lazy
      (match declaration with
      | Declaration.Constructor { identifier; _ } ->
          let declarations_rev' =
            (signature', declaration) :: signature.Signature.declarations_rev
          and bindings' =
            Identifier.Map.add identifier (signature', declaration)
              signature.Signature.bindings
          in
          {
            Signature.declarations_rev = declarations_rev';
            bindings = bindings';
          }
      | Declaration.Datatype { identifier; constructors; _ } -> (
          let declaration_bindings =
            List.fold_left add_declaration_binding
              [ (identifier, declaration) ]
              (List.rev constructors)
          in
          match
            Identifier.find_duplicates
              (List.map
                 (fun (identifier, _) -> identifier)
                 declaration_bindings)
          with
          | Option.None ->
              let declarations_rev' =
                List.map
                  (fun (_, declaration) -> (signature', declaration))
                  declaration_bindings
                @ signature.Signature.declarations_rev
              and bindings' =
                List.fold_left
                  (fun bindings (identifier, declaration) ->
                    Identifier.Map.add identifier (signature', declaration)
                      bindings)
                  signature.Signature.bindings declaration_bindings
              in
              {
                Signature.declarations_rev = declarations_rev';
                bindings = bindings';
              }
          | Option.Some duplicates -> raise (Duplicate_identifiers duplicates))
      | Declaration.Value { identifier; _ } ->
          let signature' = lazy signature in
          let declarations_rev' =
            (signature', declaration) :: signature.Signature.declarations_rev
          and bindings' =
            Identifier.Map.add identifier (signature', declaration)
              signature.Signature.bindings
          in
          {
            Signature.declarations_rev = declarations_rev';
            bindings = bindings';
          })
  in
  Lazy.force signature'

let make_signature ~declarations =
  List.fold_left add_declaration empty_signature declarations

let () =
  Printexc.register_printer (function
    | Duplicate_identifiers identifiers ->
        Option.some
          (Format.asprintf "Duplicate identifiers @[%a@] in declaration"
             (Format.pp_print_list
                ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
                Identifier.pp)
             identifiers)
    | _ -> Option.none)
