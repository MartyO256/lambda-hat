(*=
    Initial grammar:

    <variable> ::=
      | [a-z] [a-zA-Z0-9_']*

    <constant> ::=
      | [A-Z] [a-zA-Z0-9_']*

    <inf> ::=
      | `∞'
      | `inf'

    <stage> ::=
      | <variable>
      | `$'<stage>
      | <inf>

    <arrow> ::=
      | `->'
      | `→'

    <type> ::=
      | `''<variable>
      | <type> <arrow> <type>           (* Right-associative *)
      | <constant>[`^'<stage>] <type>*
      | `(' <type> `)'

    <type-without-stages> ::=
      | `''<variable>
      | <type-without-stages> <arrow> <type-without-stages>           (* Right-associative *)
      | <constant> <type-without-stages>*
      | `(' <type-without-stages> `)'

    <lambda> ::=
      | `\'
      | `λ'

    <double-arrow> ::=
      | `=>'
      | `⇒'

    <expression> ::=
      | <variable>
      | <constant>
      | <lambda><variable> [`:' <type>] `.' <expression>
      | <expression> <expression>
      | `letrec' <variable> [`:' <type>] `=' <expression>
      | `case' <expression> `of' `{' [`|'] <constant> <double-arrow> <expression> (`|' <constant> <double-arrow> <expression>)* `}'
      | <expression> `:' <type>         (* Left-associative *)
      | `(' <expression> `)'

    <datatype-declaration> ::=
      | `datatype' <constant> (`''<variable>)* `=' [`|'] <constant> `:' <type-without-stages> (`|' <constant> `:' <type>)*

    <value-declaration> ::=
      | `let' <variable> `=' <expression>

    <declaration ::=
      | <datatype-declaration>
      | <value-declaration>

    <signature> ::=
      | <declaration>*
*)

(*=
    Rewritten grammar:

    <type> ::=
      | <type1>

    <type1> ::=
      | <type2> (<arrow> <type2>)*       (* Right-associative *)

    <type2> ::=
      | <constant>[`^'<stage>] <type3>*
      | <type3>

    <type3> ::=
      | `''<variable>
      | `(' <type> `)'

    <type-without-stages> ::=
      | <type-without-stages1>

    <type-without-stages1> ::=
      | <type-without-stages2> (<arrow> <type-without-stages2>)*       (* Right-associative *)

    <type-without-stages2> ::=
      | <constant> <type-without-stages3>*
      | <type-without-stages3>

    <type-without-stages3> ::=
      | `''<variable>
      | `(' <type-without-stages> `)'

    <expression> ::=
      | <expression1>

    <expresion1> ::=
      | <lambda><variable> [`:' <type>] `.' <expression>
      | <expression2>

    <expression2> ::=
      | `letrec' <variable> [`:' <type>] `=' <expression>
      | <expression3>

    <expression3> ::=
      | <expression4> (`:' <type>)*      (* Left-associative *)

    <expression4> ::=
      | `case' <expression5> `of' `{' [`|'] <constant> <double-arrow> <expression> (`|' <constant> <double-arrow> <expression>)* `}'
      | <expression5>

    <expression5> ::=
      | <expression6> <expression6>+     (* Left-associative *)
      | <expression6>

    <expression6> ::=
      | <variable>
      | <constant>
      | `(' <expression> `)'
*)

(** {1 λ^ Parsers} *)

include Angstrom

let ascii_lambda = string "\\"
let utf8_lambda = string "λ"
let lambda = ascii_lambda <|> utf8_lambda
let ascii_arrow = string "->"
let utf8_arrow = string "→"
let arrow = ascii_arrow <|> utf8_arrow
let ascii_double_arrow = string "=>"
let utf8_double_arrow = string "⇒"
let double_arrow = ascii_double_arrow <|> utf8_double_arrow
let ascii_inf = string "inf"
let utf8_inf = string "∞"
let inf = ascii_inf <|> utf8_inf
let is_space c = match c with ' ' | '\t' -> true | _ -> false
let is_end_of_line c = match c with '\r' | '\n' -> true | _ -> false

let is_space_or_end_of_line c =
  match c with ' ' | '\t' | '\r' | '\n' -> true | _ -> false

let is_variable_start c = match c with 'a' .. 'z' -> true | _ -> false
let is_constant_start c = match c with 'A' .. 'Z' -> true | _ -> false

let is_identifier_tail c =
  match c with
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
  | _ -> false

let reserved_words = [ "let"; "letrec"; "inf"; "case"; "of"; "datatype" ]

let variable =
  let* c = peek_char_fail in
  if is_variable_start c then
    let* variable = take_while1 is_identifier_tail in
    if List.mem variable reserved_words then
      fail
        (Format.asprintf
           "\"%s\" is a reserved identifier, it cannot be used as a variable"
           variable)
    else return variable
  else fail "Expected variable"

let constant =
  let* c = peek_char_fail in
  if is_constant_start c then take_while1 is_identifier_tail
  else fail "Expected constant"

let type_variable = char '\'' *> take_while1 is_identifier_tail
let dollar = char '$'
let colon = char ':'
let dot = char '.'
let hat = char '^'
let equal = char '='
let pipe = char '|'
let left_brace = char '{'
let right_brace = char '}'
let left_parenthesis = char '('
let right_parenthesis = char ')'
let spaces = skip_while is_space_or_end_of_line
let lex p = spaces *> p <* spaces
let post_lex p = p <* spaces
let pre_lex p = spaces *> p
let in_parentheses p = left_parenthesis *> lex p <* right_parenthesis
let in_braces p = left_brace *> lex p <* right_brace
let maybe p = p >>| Option.some <|> return Option.none
let letrec_keyword = string "letrec"
let case_keyword = string "case"
let of_keyword = string "of"
let let_keyword = string "let"
let datatype_keyword = string "datatype"

let stage =
  fix (fun stage ->
      let variable =
        let* identifier = variable in
        return (Syntax_constructors.make_stage_variable identifier)
      and successor =
        let* stage = dollar *> commit *> stage in
        return (Syntax_constructors.make_stage_successor stage)
      and inf =
        let* _ = inf in
        return Syntax_constructors.make_stage_infinity
      in
      variable <|> successor <|> inf)

let type_ =
  fix (fun type_ ->
      let type3 =
        let variable =
          let* identifier = type_variable in
          return (Syntax_constructors.make_type_variable identifier)
        and parenthesized = in_parentheses type_ in
        variable <|> parenthesized
      in
      let type2 =
        let datatype =
          let* identifier = constant in
          let* stage =
            option Syntax_constructors.make_stage_infinity
              (hat *> commit *> stage)
          in
          let* arguments = many (pre_lex type3) in
          return
            (Syntax_constructors.make_type_datatype ~identifier ~stage
               ~arguments)
        in
        datatype <|> type3
      in
      let type1 =
        let* x = type2 in
        let* xs = many (lex arrow *> commit *> type2) in
        match xs with
        | [] -> return x
        | xs ->
            let last, rest =
              let[@warning "-8"] (x :: xs) = List.rev xs in
              (x, List.rev xs)
            in
            return
              (List.fold_right
                 (fun x acc ->
                   Syntax_constructors.make_type_arrow ~domain:x ~range:acc)
                 (x :: rest) last)
      in
      type1)

let type_without_stages =
  fix (fun type_ ->
      let type3 =
        let variable =
          let* identifier = type_variable in
          return (Syntax_constructors.make_type_variable identifier)
        and parenthesized = in_parentheses type_ in
        variable <|> parenthesized
      in
      let type2 =
        let datatype =
          let* identifier = constant in
          let* arguments = many (pre_lex type3) in
          return
            (Syntax_constructors.make_type_datatype ~identifier
               ~stage:Syntax_constructors.make_stage_infinity ~arguments)
        in
        datatype <|> type3
      in
      let type1 =
        let* x = type2 in
        let* xs = many (lex arrow *> commit *> type2) in
        match xs with
        | [] -> return x
        | xs ->
            let last, rest =
              let[@warning "-8"] (x :: xs) = List.rev xs in
              (x, List.rev xs)
            in
            return
              (List.fold_right
                 (fun x acc ->
                   Syntax_constructors.make_type_arrow ~domain:x ~range:acc)
                 (x :: rest) last)
      in
      type1)

let expression =
  fix (fun expression ->
      let expression6 =
        let variable =
          let* identifier = variable in
          return (Syntax_constructors.make_expression_variable identifier)
        and constant =
          let* identifier = constant in
          return (Syntax_constructors.make_expression_constructor identifier)
        and parenthesized = in_parentheses expression in
        variable <|> constant <|> parenthesized
      in
      let expression5 =
        let* x = expression6 in
        let* xs = many (pre_lex expression6) in
        match xs with
        | [] -> return x
        | xs ->
            return
              (List.fold_left
                 (fun acc x ->
                   Syntax_constructors.make_expression_application
                     ~applicand:acc ~argument:x)
                 x xs)
      in
      let expression4 =
        let case =
          let branch =
            let* c = constant in
            let* body = lex double_arrow *> expression in
            return (c, body)
          in
          let* scrutinee =
            post_lex case_keyword *> commit *> post_lex expression5
            <* post_lex of_keyword
          in
          let* branches =
            in_braces (maybe (lex pipe) *> sep_by1 (lex pipe) (pre_lex branch))
          in
          return (Syntax_constructors.make_expression_case ~scrutinee ~branches)
        in
        case <|> expression5
      in
      let expression3 =
        let* x = expression4 in
        let* xs = many (pre_lex (post_lex colon *> commit *> type_)) in
        match xs with
        | [] -> return x
        | xs ->
            return
              (List.fold_left
                 (fun acc x ->
                   Syntax_constructors.make_expression_annotated ~expression:acc
                     ~type_:x)
                 x xs)
      in
      let expression2 =
        let letrec =
          let* identifier =
            post_lex letrec_keyword *> commit *> post_lex variable
          in
          let* type_ = maybe (colon *> commit *> lex type_) in
          let* expression = equal *> pre_lex expression in
          return
            (Syntax_constructors.make_expression_rec ~identifier ~type_
               ~expression)
        in
        letrec <|> expression3
      in
      let expression1 =
        let abstraction =
          let* parameter_identifier = lambda *> commit *> post_lex variable in
          let* parameter_type = maybe (colon *> commit *> lex type_) in
          let* body = dot *> pre_lex expression in
          return
            (Syntax_constructors.make_expression_abstraction
               ~parameter_identifier ~parameter_type ~body)
        in
        abstraction <|> expression2
      in
      expression1)

let datatype_declaration =
  let* identifier = post_lex datatype_keyword *> commit *> constant in
  let* parameters = many (pre_lex type_variable) in
  let constructor_declaration =
    let* identifier = constant in
    let* type_ = lex colon *> type_without_stages in
    return (Syntax_constructors.make_declaration_constructor ~identifier ~type_)
  in
  let* constructors =
    lex equal
    *> maybe (lex pipe)
    *> sep_by1 (lex pipe) (pre_lex constructor_declaration)
  in
  return
    (Syntax_constructors.make_declaration_datatype ~identifier ~parameters
       ~constructors)

let value_declaration =
  let* identifier = post_lex let_keyword *> commit *> variable in
  let* expression = lex equal *> expression in
  return (Syntax_constructors.make_declaration_value ~identifier ~expression)

let declaration = datatype_declaration <|> value_declaration

let signature =
  let* declarations = many (post_lex declaration) in
  return (Syntax_constructors.make_signature ~declarations)
