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
