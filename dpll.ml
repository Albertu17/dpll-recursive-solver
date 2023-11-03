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
(* let () = print_modele (solveur_split systeme [])
let () = print_modele (solveur_split exemple_3_12 [])
let () = print_modele (solveur_split exemple_7_2 [])
let () = print_modele (solveur_split exemple_7_4 [])
let () = print_modele (solveur_split exemple_7_8 [])
let () = print_modele (solveur_split coloriage [])  *)

(* solveur dpll récursif *)
(* ----------------------------------------------------------- *)

(* count_abs_occ : int list -> int -> int * int 
    prend en argument une liste l et un entier x,
    compte le nombre d'occurences c de x dans l
    et le nombre d'occurences c' de -x dans l,
    et retourne le couple (c,c').
  *)
let count_abs_occ l x = 
  let rec aux l (c,c') = match l with
    | [] -> (c,c')
    | h::t -> if h=x then aux t (c+1,c')
        else if h=(-x) then aux t (c,c'+1)
        else aux t (c,c') 
  in aux l (0,0)

(* pur : int list list -> (int, int) Result.t
    - si `clauses' contient au moins un littéral pur l, retourne
    ce littéral sous la forme Ok(l).
    - sinon, retourne le littéral x ayant le plus d'occurences
    parmi les clauses (en comptant sa forme opposée) sous la
    forme Error(x).
*) 
let pur clauses = 
  (* paramètres de la fonction auxiliaire:
    l: liste (applatie) de littéraux.
    (x, occ_x): élément le plus présent parmi la liste,
      son nombre d'occurences. *)
  let rec aux l (x,occ_x) = match l with
    | [] -> Error(x) (* Si on est arrivé jusqu'à la fin
      de la liste, alors elle ne comprenait pas d'élément
      pur: on renvoie celui ayant le plus d'occurences. *)
    | h::t -> let (c,c') = count_abs_occ l h in
        if c'=0 then Ok(h) (* Si l'opposé du littéral h
          n'est pas présent parmi les clauses, alors h est
          pur, on le renvoie.*)
        else let occ_h = c+c' in (* Sinon, on poursuit la recherche
           dans la liste privée des occurences de h, avec comme
           élément le plus présent pour l'instant h ou x, selon le
           résultat de la comparaison entre occ_h et occ_x. *)
          aux (filter (fun y -> y!=h && y!=(-h)) t)
          (if occ_h > occ_x then (h,occ_h) else (x,occ_x))
  in let flat = flatten clauses
  (* On passe à la fonction auxiliaire les clauses réunient dans
    une seule liste applatie, ainsi que l'élément a priori le plus
    présent dans cette liste: le premier. *)
  in aux flat ((hd flat), 1)

(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)
let rec unitaire clauses = match clauses with
  | [] -> raise Not_found
  | h::t -> (match h with
    | [l] -> l (* Si une clause unitaire est trouvée, on renvoie
       son littéral.*)
    | _ -> unitaire t) (* Sinon, on passe à l'examen de la clause
       suivante.*)

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  (* Conditions de terminaison *)
  if clauses = [] then Some interpretation else
  if mem [] clauses then None else
  (* Règle unit *)
  try
    let littUnit = unitaire clauses in
    solveur_dpll_rec (simplifie littUnit clauses) (littUnit::interpretation)
  with Not_found ->
  (* Règle pure *)
  match pur clauses with
    | Ok(littPur) -> solveur_dpll_rec (simplifie littPur clauses) (littPur::interpretation)
    | Error(l) -> (* l est le littéral le plus présent parmi toutes les clauses. *)
  (* Branchement (avec l) *)
      let branche = solveur_dpll_rec (simplifie l clauses) (l::interpretation) in
      match branche with
        | None -> solveur_dpll_rec (simplifie (-l) clauses) ((-l)::interpretation)
        | _    -> branche

(* tests *)
(* ----------------------------------------------------------- *)
(* let () = print_modele (solveur_dpll_rec systeme [])
let () = print_modele (solveur_dpll_rec exemple_3_12 [])
let () = print_modele (solveur_dpll_rec exemple_7_2 [])
let () = print_modele (solveur_dpll_rec exemple_7_4 [])
let () = print_modele (solveur_dpll_rec exemple_7_8 [])
let () = print_modele (solveur_dpll_rec coloriage []) *)
let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
