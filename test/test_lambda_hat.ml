open Lambda_hat

let parse_stage token =
  Result.get_ok
    (Parser.parse_string ~consume:Parser.Consume.All (Parser.lex Parser.stage)
       token)

let parse_type token =
  Result.get_ok
    (Parser.parse_string ~consume:Parser.Consume.All (Parser.lex Parser.type_)
       token)

let parse_expression token =
  Result.get_ok
    (Parser.parse_string ~consume:Parser.Consume.All
       (Parser.lex Parser.expression)
       token)

let parse_declaration token =
  Result.get_ok
    (Parser.parse_string ~consume:Parser.Consume.All
       (Parser.lex Parser.declaration)
       token)

let parse_signature token =
  Result.get_ok
    (Parser.parse_string ~consume:Parser.Consume.All
       (Parser.lex Parser.signature)
       token)

let () =
  [ "s"; "$s"; "inf"; "$$s"; "$inf" ]
  |> List.iter (fun token ->
         Format.fprintf Format.std_formatter "Parsing stage@ \"%s\"@ to@ %a@."
           token
           (Yojson.Safe.pretty_print ~std:true)
           (Syntax.json_of_stage (parse_stage token)))

let () =
  [
    "'a";
    "('b)";
    "Bool";
    "List^i 'a";
    "List^$i 'a";
    "List^inf 'a";
    "Pair^i 'a 'b";
    "'a -> 'b";
    "'a -> 'b -> 'c";
    "'a -> ('b -> 'c)";
    "('a -> 'b) -> 'c";
  ]
  |> List.iter (fun token ->
         Format.fprintf Format.std_formatter "Parsing type@ \"%s\"@ to@ %a@."
           token
           (Yojson.Safe.pretty_print ~std:true)
           (Syntax.json_of_type (parse_type token)))

let () =
  [
    "x";
    "O";
    {|\x. x|};
    {|\x : Nat. x|};
    {|\x : Nat^$i. \y : Nat. x y|};
    {|\x : Nat. x|};
    "case x of { O => y }";
    "case x of { | O => y }";
    "case x of { | O => y | O => y }";
    {|case x of { S => \x' : Nat^i. S (plus x' y) }|};
    "letrec plus = plus";
    "letrec plus : Nat^i -> Nat -> Nat = plus";
    {|
    letrec plus : Nat^i -> Nat -> Nat =
      \x : Nat^$i. \y : Nat. case x of {
        | O => y
        | S => \x' : Nat^i. S (plus x' y)
      }
    |};
  ]
  |> List.iter (fun token ->
         Format.fprintf Format.std_formatter
           "Parses expression@ \"%s\"@ to@ %a@." token
           (Yojson.Safe.pretty_print ~std:true)
           (Syntax.json_of_expression (parse_expression token)))

let () =
  []
  |> List.iter (fun token ->
         Format.fprintf Format.std_formatter "%a@."
           (Yojson.Safe.pretty_print ~std:true)
           (Syntax.json_of_declaration (parse_declaration token)))

let () =
  [
    {|
datatype Bool =
  | True : Bool
  | False : Bool

datatype Nat =
  | O : Nat
  | S : Nat -> Nat

datatype List 'a =
  | Nil : List 'a
  | Cons : 'a -> List 'a -> List 'a

datatype Tree 'a =
  | Branch : 'a -> List (Tree 'a) -> Tree 'a

datatype Ord =
  | Zero : Ord
  | Succ : Ord -> Ord
  | Lim : (Nat -> Ord) -> Ord

let plus =
  letrec plus : Nat^i -> Nat -> Nat =
    \x : Nat^$i. \y : Nat. case x of {
      | O => y
      | S => \x' : Nat^i. S (plus x' y)
    }

let append =
  letrec append : List^i 'a -> List 'a -> List 'a =
    \x : List^$i 'a. \y : List 'a. case x of {
      | Nil => y
      | Cons => \z : 'a. \x' : List^i 'a. Cons z (append x' y)
    }

let conc =
  letrec conc : List^i (List 'a) -> List 'a =
    \x : List^$i (List 'a). case x of {
      | Nil => Nil
      | Cons => \z : List 'a. \x' : List^i (List 'a). append z (conc x')
    }

let add =
  letrec add : Ord^i -> Ord -> Ord =
    \x : Ord^$i. \y : Ord. case x of {
      | Zero => y
      | Succ => \x' : Ord^i. Succ (add x' y)
      | Lim => \x' : Nat -> Ord^i. Lim (\z : Nat. add (x' z) y)
    }

let even =
  letrec even : Nat^i -> Bool =
    \x : Nat^$i. case x of {
      | O => True
      | S => \x' : Nat^i. case x' of {
        | O => False
        | S => \x'' : Nat^i. even x''
      }
    }

let length =
  letrec length : List^i 'a -> Nat^i =
    \x : List^$i 'a. case x of {
      | Nil => O
      | Cons => \z : 'a. \x' : List^i 'a. S (length x')
    }

let map =
  \f : 'a -> 'b.
    letrec map : List^i 'a -> List^i 'b =
      \x : List^$i 'a. case x of {
        | Nil => Nil
        | Cons => \z : 'a. \x' : List^i 'a. Cons (f z) (map x')
      }

let minus =
  letrec minus : Nat^i -> Nat -> Nat^i =
    \x : Nat^$i. \y : Nat. case x of {
      | O => x
      | S => \x' : Nat^i. case y of {
        | O => x
        | S => \y' : Nat. minus x' y'
      }
    }

let div =
  letrec div : Nat^i -> Nat -> Nat^i =
    \x : Nat^$i. \y : Nat. case x of {
      | O => O
      | S => \x' : Nat^i. S (div (minus x' y) y)
    }

let flatten =
  letrec flatten : Tree^i 'a -> List 'a =
    \x : Tree^$i 'a. case x of {
      | Branch => \z : 'a. \x' : List (Tree^i 'a). Cons z (conc (map flatten x'))
    }

let ack =
  letrec ack : Nat^i -> Nat -> Nat =
    \x : Nat^$i. case x of {
      | O => \z : Nat. (S z)
      | S => \x' : Nat^i. letrec ack_x : Nat^j -> Nat =
        \y : Nat^$j. case y of {
          | O => ack x' (S O)
          | S => \y' : Nat^j. ack x' (ack_x y')
        }
    }
|};
    {|
datatype Bool =
  | True : Bool
  | False : Bool

datatype Nat =
  | O : Nat
  | S : Nat -> Nat

datatype List 'a =
  | Nil : List 'a
  | Cons : 'a -> List 'a -> List 'a

datatype Tree 'a =
  | Branch : 'a -> List (Tree 'a) -> Tree 'a

datatype Ord =
  | Zero : Ord
  | Succ : Ord -> Ord
  | Lim : (Nat -> Ord) -> Ord

let plus =
  letrec plus =
    \x. \y. case x of {
      | O => y
      | S => \x'. S (plus x' y)
    }

let append =
  letrec append =
    \x. \y. case x of {
      | Nil => y
      | Cons => \z. \x'. Cons z (append x' y)
    }

let conc =
  letrec conc =
    \x. case x of {
      | Nil => Nil
      | Cons => \z. \x'. append z (conc x')
    }

let add =
  letrec add =
    \x. \y. case x of {
      | Zero => y
      | Succ => \x'. Succ (add x' y)
      | Lim => \x'. Lim (\z : Nat. add (x' z) y)
    }

let even =
  letrec even =
    \x. case x of {
      | O => True
      | S => \x'. case x' of {
        | O => False
        | S => \x''. even x''
      }
    }

let length =
  letrec length =
    \x. case x of {
      | Nil => O
      | Cons => \z. \x'. S (length x')
    }

let map =
  \f.
    letrec map =
      \x. case x of {
        | Nil => Nil
        | Cons => \z. \x'. Cons (f z) (map x')
      }

let minus =
  letrec minus =
    \x. \y. case x of {
      | O => x
      | S => \x'. case y of {
        | O => x
        | S => \y'. minus x' y'
      }
    }

let div =
  letrec div =
    \x. \y. case x of {
      | O => O
      | S => \x'. S (div (minus x' y) y)
    }

let flatten =
  letrec flatten =
    \x. case x of {
      | Branch => \z. \x'. Cons z (conc (map flatten x'))
    }

let ack =
  letrec ack =
    \x. case x of {
      | O => \z. (S z)
      | S => \x'. letrec ack_x =
        \y. case y of {
          | O => ack x' (S O)
          | S => \y'. ack x' (ack_x y')
        }
    }
|};
  ]
  |> List.iter (fun token ->
         Format.fprintf Format.std_formatter
           "Parses signature@ \"%s\"@ to@ %a@." token
           (Yojson.Safe.pretty_print ~std:true)
           (Syntax.json_of_signature (parse_signature token));
         Format.fprintf Format.std_formatter
           "Parses signature@ \"%s\"@ to@ %a@." token Syntax.pp_signature
           (parse_signature token))
