open Syntax

exception
  Unbound_identifier of { signature : signature; identifier : identifier }

exception Unbound_datatype of { signature : signature; identifier : identifier }

exception
  Unbound_constructor of { signature : signature; identifier : identifier }

exception Unbound_value of { signature : signature; identifier : identifier }

exception
  Expected_datatype_declaration of {
    signature : signature;
    identifier : identifier;
    declaration : declaration;
  }

exception
  Expected_constructor_declaration of {
    signature : signature;
    identifier : identifier;
    declaration : declaration;
  }

exception
  Expected_value_declaration of {
    signature : signature;
    identifier : identifier;
    declaration : declaration;
  }

let[@inline] lookup_signature_opt signature identifier =
  let { Signature.bindings; _ } = signature in
  Identifier.Map.find_opt identifier bindings

let[@inline] lookup_signature signature identifier =
  match lookup_signature_opt signature identifier with
  | Option.Some (_, declaration) -> declaration
  | Option.None -> raise (Unbound_identifier { signature; identifier })

let lookup_constructor signature constructor_identifier =
  match lookup_signature_opt signature constructor_identifier with
  | Option.Some (_, Declaration.Constructor { identifier; type_ }) ->
      (identifier, type_)
  | Option.Some (_, declaration) ->
      raise
        (Expected_constructor_declaration
           { signature; identifier = constructor_identifier; declaration })
  | Option.None ->
      raise
        (Unbound_constructor { signature; identifier = constructor_identifier })

let lookup_datatype signature datatype_identifier =
  match lookup_signature_opt signature datatype_identifier with
  | Option.Some
      (_, Declaration.Datatype { identifier; parameters; constructors }) ->
      (identifier, parameters, constructors)
  | Option.Some (_, declaration) ->
      raise
        (Expected_datatype_declaration
           { signature; identifier = datatype_identifier; declaration })
  | Option.None ->
      raise (Unbound_datatype { signature; identifier = datatype_identifier })

let lookup_value signature value_identifier =
  match lookup_signature_opt signature value_identifier with
  | Option.Some (_, Declaration.Value { identifier; expression }) ->
      (identifier, expression)
  | Option.Some (_, declaration) ->
      raise
        (Expected_value_declaration
           { signature; identifier = value_identifier; declaration })
  | Option.None ->
      raise (Unbound_value { signature; identifier = value_identifier })

let () =
  Printexc.register_printer (function
    | Unbound_identifier { identifier; _ } ->
        Option.some
          (Format.asprintf "Identifier @[%a@] is unbound" Identifier.pp
             identifier)
    | Unbound_constructor { identifier; _ } ->
        Option.some
          (Format.asprintf "Constructor @[%a@] is unbound" Identifier.pp
             identifier)
    | Unbound_datatype { identifier; _ } ->
        Option.some
          (Format.asprintf "Datatype @[%a@] is unbound" Identifier.pp identifier)
    | Unbound_value { identifier; _ } ->
        Option.some
          (Format.asprintf "Value @[%a@] is unbound" Identifier.pp identifier)
    | Expected_datatype_declaration { identifier; declaration; _ } ->
        Option.some
          (Format.asprintf
             "Expected a datatype declaration @[%a@] but got @[%a@]"
             Identifier.pp identifier Syntax_pp.pp_declaration declaration)
    | Expected_constructor_declaration { identifier; declaration; _ } ->
        Option.some
          (Format.asprintf
             "Expected a constructor declaration @[%a@] but got @[%a@]"
             Identifier.pp identifier Syntax_pp.pp_declaration declaration)
    | Expected_value_declaration { identifier; declaration; _ } ->
        Option.some
          (Format.asprintf "Expected a value declaration @[%a@] but got @[%a@]"
             Identifier.pp identifier Syntax_pp.pp_declaration declaration)
    | _ -> Option.none)
