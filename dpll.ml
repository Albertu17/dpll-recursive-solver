(* MP1 2023/2024 - dpll.ml *)

open List

(* fonctions utilitaires *)
(* ----------------------------------------------------------- *)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [
  [1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];
  [19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];
  [-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];
  [-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];
  [-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];
  [-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];
  [-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];
  [-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];
  [-14;-17];[-15;-18]]

(* ----------------------------------------------------------- *)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)
let simplifie l clauses =
  (* simplifieClause : int list -> int list option
     simplifie une seule clause. Est adaptée pour être passée en
     argument à filter_map. *)
  let simplifieClause clause = 
    let rec aux clause acc = match clause with
      | [] -> Some(acc)
      | h::t ->
        if h=l then None (* Si un des éléments de la clause est l,
          on renvoie None. La clause sera supprimée dans le
          résultat de filter_map. *)
        else if h=(-l) then aux t acc (* Si un des éléménts est -l,
          on ne le reporte pas dans la simplification. *)
        else aux t (h::acc) (* Sinon, on reporte l'élément dans la
           simplification. *)
    in aux clause []
  in filter_map simplifieClause clauses

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* la clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
let () = print_modele (solveur_split systeme [])
let () = print_modele (solveur_split exemple_3_12 [])
let () = print_modele (solveur_split exemple_7_2 [])
let () = print_modele (solveur_split exemple_7_4 [])
let () = print_modele (solveur_split exemple_7_8 [])
(let () = print_modele (solveur_split coloriage []) 

(* solveur dpll récursif *)
(* ----------------------------------------------------------- *)

(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)


(* custom exception to be used to raise (Failure "pas de littéral pur") *)
exception Failure of string;;


(* pur : int list list -> int
    - si `clauses' contient au moins littéral, retourne ce littéral
    - sinon, lève une exception `Failure "pas de littéral pur"
*)
let pur clauses = let l = List.flatten clauses in 
  let sch = searchPur l 0 (List.length l) in 
  if sch = 0 then raise (Failure "pas de littéral pur") else sch


(* searchPur : int list -> int -> int -> int
    - si 'flat' ne contient pas l'inverse du littéral d'index n, s'appelle recursivement en incrémentant l'index de 1
    - si n + 1 est supérieuse à la longeur length de la liste aplatie, alors il n'existe pas de litéral pur, et 
        la fonction lève une exception Failure "pas de littéral pur"
    - si 'flat' en contient pas l'inverse du littéral d'index n, alors ce littéral est pur, et est retourné.
 *)
let rec searchPur flat n length = match List.find_opt ((fun item -> item = - (List.nth flat n))) flat with
  | None -> List.nth flat n
  | l -> if (n + 1) >= length then raise (Failure "pas de littéral pur") else searchPur flat (n + 1) length


(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)
let rec unitaire clauses = match clauses with
  | [] -> raise Not_found
  | h::t -> match h with
    | [l] -> l (* Si une clause unitaire est trouvée, renvoie son littéral.*)
    | _ -> unitaire t (* Sinon, passe à l'examen de la clause suivante.*)

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  (* Conditions de terminaison *)
  if clauses = [] then Some interpretation else
  if mem [] clauses then None else
  (* Règle unit *)
  try
    let littUnit = unitaire clauses in
    solveur_dpll_rec (simplifie littUnit clauses) interpretation
  with Not_found ->
  (* Règle pure *)
  try
    let littPur = pur clauses in
    solveur_dpll_rec (simplifie littPur clauses) interpretation
  with Failure _ ->
  (* Branchement *)
  let l = hd (hd clauses) in (* TODO: Comment optimiser le choix de p ? *)
  let branche = solveur_dpll_rec (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_dpll_rec (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(* ----------------------------------------------------------- *)
(* let () = print_modele (solveur_dpll_rec systeme []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)

(* let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses []) *)
