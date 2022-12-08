module rec Stage : sig
  type t =
    | Variable of { identifier : Identifier.t }
    | Successor of { stage : Stage.t }
    | Infinity
    | Closure of { stage : Stage.t; environment : Stage.t Identifier.Map.t }
end =
  Stage

and Type : sig
  type t =
    | Variable of { identifier : Identifier.t }
    | Arrow of { domain : Type.t; range : Type.t }
    | Datatype of {
        identifier : Identifier.t;
        stage : Stage.t;
        arguments : Type.t List.t;
      }
    | Closure of { type_ : Type.t; environment : Type.t Identifier.Map.t }
end =
  Type

and Expression : sig
  type t =
    | Variable of { identifier : Identifier.t }
    | Constructor of { identifier : Identifier.t }
    | Abstraction of {
        parameter_identifier : Identifier.t;
        parameter_type : Type.t Option.t;
        body : Expression.t;
      }
    | Application of { applicand : Expression.t; argument : Expression.t }
    | Case of {
        scrutinee : Expression.t;
        branches : (Identifier.t * Expression.t) List.t;
      }
    | Rec of {
        identifier : Identifier.t;
        type_ : Type.t Option.t;
        expression : Expression.t;
      }
    | Annotated of { expression : Expression.t; type_ : Type.t }
    | Closure of {
        expression : Expression.t;
        environment : Expression.t Identifier.Map.t;
      }
end =
  Expression

and Declaration : sig
  type t =
    | Constructor of { identifier : Identifier.t; type_ : Type.t }
    | Datatype of {
        identifier : Identifier.t;
        parameters : Identifier.t List.t;
        constructors : Declaration.t List.t;
      }
    | Value of { identifier : Identifier.t; expression : Expression.t }
end =
  Declaration

and Signature : sig
  type t = {
    declarations_rev : (Signature.t Lazy.t * Declaration.t) List.t;
    bindings : (Signature.t Lazy.t * Declaration.t) Identifier.Map.t;
  }
end =
  Signature

type identifier = Identifier.t
type stage = Stage.t
type type_ = Type.t
type expression = Expression.t
type declaration = Declaration.t
type signature = Signature.t

exception Malformed_stage of stage
exception Malformed_type of type_
exception Malformed_expression of expression
exception Malformed_declaration of declaration
exception Malformed_signature of signature

let () =
  Printexc.register_printer (function
    | Malformed_stage _ ->
        Option.some (Format.asprintf "Encountered a malformed stage")
    | Malformed_type _ ->
        Option.some (Format.asprintf "Encountered a malformed type")
    | Malformed_expression _ ->
        Option.some (Format.asprintf "Encountered a malformed expression")
    | Malformed_declaration _ ->
        Option.some (Format.asprintf "Encountered a malformed declaration")
    | Malformed_signature _ ->
        Option.some (Format.asprintf "Encountered a malformed signature")
    | _ -> Option.none)
