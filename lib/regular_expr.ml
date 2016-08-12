(** This file is part of the MemCAD analyzer
 **
 ** GNU General Public License
 **
 ** Version v2016.03.00, March 2016
 ** Authors: Xavier Rival, Francois Berenger, Huisong Li, Jiangchao Liu,
 **          Pascal Sotin, Antoine Toubhans, Pippijn Van Steenhoeven
 ** Copyright (c) 2016 INRIA
 **
 ** File: regular_expr.ml
 **       generic regular expression
 ** Antoine Toubhans, 2012/05/29 *)
open Data_structures
open Flags
open Lib

(** main type *)
type 'a t = 
  (* empty set of words *)
  | Reg_zero 
  (* singleton empty word *)
  | Reg_one  
  (* singleton label a *)
  | Reg_label of 'a
  (* concatenation *)
  | Reg_conc of 'a t * 'a t
  (* union *)
  | Reg_plus of 'a t * 'a t
  (* sequence *)
  | Reg_star of 'a t

(** type used to simplify regex:
 *  . * are moved up to top 
 *  . no concat            *)
type 'a s =
  (* 1 *)
  | St_one
  (* a1+a2+...+an *)
  | St_plus of 'a PSet.t
  (* (a1+..+an)^* *)
  | St_star of 'a PSet.t

(** constructors *)
(* 0 *)
let zero: 'a t = Reg_zero
(* 1 *)
let one: 'a t = Reg_one
(* a -> a *)
let label (a: 'a): 'a t = Reg_label a
(* L1 -> L2 -> L1+L2 *)
let plus (x: 'a t) (y: 'a t): 'a t = Reg_plus (x, y)
(* L1 -> L2 -> L1.L2 *)
let concat (x: 'a t) (y: 'a t): 'a t = Reg_conc (x, y)
(* L -> L* *)
let star (x: 'a t): 'a t = Reg_star x
(* { a1, ..., an } -> (a1+...+an)* *)
let set_2t (s: 'a PSet.t): 'a t =
  if PSet.is_empty s then Reg_zero
  else
    let a = PSet.choose s in
    let s = PSet.remove a s in
    PSet.fold (fun a t -> Reg_plus (Reg_label a, t)) s (Reg_label a) 

(** pretty printing *)
let rec t_2str (f: 'a -> string): 'a t -> string = function
  | Reg_zero -> "0"
  | Reg_one -> "1"
  | Reg_label a -> f a
  | Reg_conc (x, y) -> 
      Printf.sprintf "( %s ).( %s )" (t_2str f x) (t_2str f y)
  | Reg_plus (x, y) -> 
      Printf.sprintf "%s+%s" (t_2str f x) (t_2str f y)
  | Reg_star (Reg_label a) ->
      Printf.sprintf "%s*" (f a) 
  | Reg_star x -> 
      Printf.sprintf "(%s)*" (t_2str f x) 
  
(** testing tools *)
let is_label: 'a t -> 'a option = function
  | Reg_label x -> Some x
  | _ -> None
(* A regular expression is rigid iff its corresponding set of words
 *   is a singleton.
 * function "is_rigid" is conservative,
 *   e.g., it returns false on "0 + 1" *)
let rec is_rigid: 'a t -> bool = function
  | Reg_one -> true
  | Reg_label _ -> true
  | Reg_conc (x, y) -> is_rigid x && is_rigid y
  | _ -> false
(* F regular expression is finite
 *   iff its corresponding set of words is finite
 * function "is_finite" is conservative;
 *   e.g., it returns false on "0*" or "1*" *)
let rec is_finite: 'a t -> bool = function
  | Reg_zero | Reg_one | Reg_label _ -> true
  | Reg_plus (x, y)
  | Reg_conc (x, y) -> is_finite x && is_finite y
  | Reg_star _ -> false 
(* does the empty word belong to the set of words corresponding
 * to some regular expression *)
let rec has_empty: 'a t -> bool = function
  | Reg_one | Reg_star _ -> true
  | Reg_plus (x, y) -> has_empty x || has_empty y
  | Reg_conc (x, y) -> has_empty x && has_empty y
  | Reg_zero | Reg_label _ -> false

(** comparison tools *)
(* language inclusion (conservative) *)
let rec is_le (rl: 'a t) (rr: 'a t): bool = 
  match rl, rr with
  | Reg_zero, _
  | Reg_one, Reg_one
  | Reg_one, Reg_star _ -> true
  | Reg_plus (x, y), _ -> is_le x rr && is_le y rr
  | _, Reg_plus (x, y) -> is_le rl x || is_le rl y
  | Reg_conc (x, y), Reg_star _ -> is_le x rr && is_le y rr      
  | Reg_star x, Reg_star y -> is_le x y
  | _, Reg_star z -> is_le rl z 
  | Reg_label a, Reg_label b ->
      (* consider adding eq function *) a = b
  | _ -> false
(* semantic equality (conservative) *)
let eq (rl: 'a t) (rr: 'a t): bool = 
  is_le rl rr && is_le rr rl

(** operation on simplified type 's *)
let s_plus (x: 'a s) (y: 'a s): 'a s = 
  match x, y with
  | St_one, St_one -> St_one
  | St_one, St_plus s
  | St_one, St_star s
  | St_plus s, St_one
  | St_star s, St_one -> St_star s
  | St_plus s1, St_plus s2 -> St_plus (PSet.union s1 s2)
  | St_plus s1, St_star s2
  | St_star s1, St_plus s2
  | St_star s1, St_star s2 -> St_star (PSet.union s1 s2)

let s_conc (x: 'a s) (y: 'a s): 'a s = 
  match x, y with
  | St_one, z | z, St_one -> z
  | St_plus s1, St_plus s2
  | St_plus s1, St_star s2
  | St_star s1, St_plus s2
  | St_star s1, St_star s2 -> St_star (PSet.union s1 s2)

let s_star: 'a s -> 'a s = function 
  | St_one -> St_one
  | St_plus s -> if PSet.is_empty s then St_one else St_star s
  | St_star s -> St_star s

(** transformation 's <-> 't tools *)
(* cast a regular expression 't into
 * a simplified regular expression 's *)
let rec t_2s: 'a t -> 'a s = function
  | Reg_zero        -> St_plus PSet.empty
  | Reg_one         -> St_one
  | Reg_label a     -> St_plus (PSet.singleton a)
  | Reg_plus (x, y) -> s_plus (t_2s x) (t_2s y)       
  | Reg_conc (x, y) -> s_conc (t_2s x) (t_2s y)       
  | Reg_star x      -> s_star (t_2s x)
(* cast a simplified regular expression 's
 * into a regular expression 't *)
let s_2t: 'a s -> 'a t = function
  | St_one    -> Reg_one
  | St_plus s -> set_2t s
  | St_star s -> Reg_star (set_2t s)

(** transformation tools *)
(* simplifying (with a possible approximation) *)
let simplify: 'a t -> 'a t = fun t -> s_2t (t_2s t)
(* find generators of language L i.e
 * labels { a1, a2, ... an } such that
 * L <= 1 + a1.L + ... + an.L *)
let generators (reg: 'a t): 'a PSet.t =
  let sreg: 'a s = t_2s reg in
  match sreg with
  | St_one -> PSet.empty
  | St_plus s | St_star s -> s
