type t = string

let show s = s
let pp = Format.pp_print_string
let equal = ( = )
let make s = s

module Set = Set.Make (String)
module Map = Map.Make (String)

let inspect_duplicates identifiers =
  let duplicates, set =
    List.fold_left
      (fun (duplicates, encountered_identifiers) addition ->
        match Set.find_opt addition encountered_identifiers with
        | Option.Some hit ->
            let duplicates' = addition :: hit :: duplicates in
            (duplicates', encountered_identifiers)
        | Option.None ->
            let encountered_identifiers' =
              Set.add addition encountered_identifiers
            in
            (duplicates, encountered_identifiers'))
      ([], Set.empty) identifiers
  in
  match duplicates with
  | _e1 :: _e2 :: _es -> (Option.some duplicates, set)
  | [] -> (Option.none, set)
  | _ -> assert false

let find_duplicates identifiers =
  let duplicates, _ = inspect_duplicates identifiers in
  duplicates
