
open Ast
open Format

(* Exception raised to report error during interpretation *)
exception Error of string
let error s = raise (Error s)

(* The values of Mini-Python

   - a noticeable difference with Python: we
      here uses the int type while the Python integers are of
      arbitrary precision; we could use OCaml's Big_int module
      but we choose the facility
   - what Python calls a list is actually a table
      resizable; in the fragment considered here, there is no
      possibility of changing the length, so a simple table OCaml
      appropriate *)
type value =
  | Vnone
  | Vbool of bool
  | Vint of int
  | Vstring of string
  | Vlist of value array

(* Displaying a value on the standard output *)
let rec print_value = function
  | Vnone -> printf "None"
  | Vbool true -> printf "True"
  | Vbool false -> printf "False"
  | Vint n -> printf "%d" n
  | Vstring s -> printf "%s" s
  | Vlist a ->
    let n = Array.length a in
    printf "[";
    for i = 0 to n-1 do print_value a.(i); if i < n-1 then printf ", " done;
    printf "]"

(* Boolean interpretation of a value

   In Python, any value can be used as a Boolean: None,
   the empty list, the empty string, and the integer 0 are considered
   False and any other values like True *)

let is_false v = match v with
  | Vnone -> true
  | Vint b when b == 0 -> true
  | Vstring s when s == "" -> true
  | Vlist a -> Array.length a == 0
  | Vbool b -> not b
  | _ -> false

let is_true v = not (is_false v)

(* The functions here are only global *)

let functions = (Hashtbl.create 16 : (string, ident list * stmt) Hashtbl.t)

(* The 'return' statement of Python is interpreted using an exception *)

exception Return of value
let return s = raise (Return s)

(* Local variables (function parameters and variables introduced
   assignments) are stored in a hash table passed in
   arguments to the following functions under the name 'ctx' *)

type ctx = (string, value) Hashtbl.t

(* Interpreting an expression (return a value) *)

let compare_value v1 v2 =
  match v1, v2 with
    | Vnone, Vnone -> 0
    | Vbool b1, Vbool b2 -> compare b1 b2
    | Vint i1, Vint i2 -> compare i1 i2
    | Vstring s1, Vstring s2 -> compare s1 s2
    | Vlist l1, Vlist l2 ->
      let len1 = Array.length l1 in
      let len2 = Array.length l2 in
      let rec compare_vlist n =
        if n == len1 || n == len2 then compare len1 len2
        else begin
          let t = compare (Array.get l1 n) (Array.get l2 n) in
          if t != 0 then t
          else compare_vlist (n+1)
        end
      in compare_vlist 0
    | _ -> error "unsupported operand types for compare"

let vlist_idx l i =
  let n = Array.length l in
  let check i =
    if i < 0 || i >= n then
      error "list index out of range"
    else
      i
  in if i < 0 then
    check (n+i)
  else
    check i

let rec expr ctx = function
  | Ecst Cnone ->
      Vnone
  | Ecst (Cstring s) ->
      Vstring s
  (* arithmetic *)
  | Ecst (Cint n) ->
      Vint n
  | Ebinop (Badd | Bsub | Bmul | Bdiv | Bmod |
            Beq | Bneq | Blt | Ble | Bgt | Bge as op, e1, e2) ->
      let v1 = expr ctx e1 in
      let v2 = expr ctx e2 in
      begin match op, v1, v2 with
        | Badd, Vint n1, Vint n2 -> Vint (n1+n2)
        | Bsub, Vint n1, Vint n2 -> Vint (n1-n2)
        | Bmul, Vint n1, Vint n2 -> Vint (n1*n2)
        | Bdiv, Vint n1, Vint n2 -> Vint (n1/n2)
        | Bmod, Vint n1, Vint n2 -> Vint (n1 mod n2)
        | Beq, _, _  -> Vbool (compare_value v1 v2 = 0)
        | Bneq, _, _ -> Vbool (compare_value v1 v2 != 0)
        | Blt, _, _  -> Vbool (compare_value v1 v2 < 0)
        | Ble, _, _  -> Vbool (compare_value v1 v2 <= 0)
        | Bgt, _, _  -> Vbool (compare_value v1 v2 > 0)
        | Bge, _, _  -> Vbool (compare_value v1 v2 >= 0)
        | Badd, Vstring s1, Vstring s2 ->
            Vstring (s1^s2)
        | Badd, Vlist l1, Vlist l2 ->
            Vlist (Array.append l1 l2)
        | _ -> error "unsupported operand types for binop"
      end
  | Eunop (Uneg, e1) ->
      let v1 = expr ctx e1 in
      begin match v1 with
        | Vint n1 -> Vint (-n1)
        | _ -> error "unsupported operand types for -i"
      end
  (* booleans *)
  | Ecst (Cbool b) ->
      Vbool (b)
  | Ebinop (Band, e1, e2) ->
      Vbool (is_true (expr ctx e1) && is_true (expr ctx e2))
  | Ebinop (Bor, e1, e2) ->
      Vbool (is_true (expr ctx e1) || is_true (expr ctx e2))
  | Eunop (Unot, e1) ->
      Vbool (is_false (expr ctx e1))
  | Eident id ->
      Hashtbl.find ctx id
  (* function call *)
  | Ecall ("len", [e1]) ->
      let v1 = expr ctx e1 in
      begin match v1 with
        | Vlist l -> Vint (Array.length l)
        | _ -> error "unsupported operand types for len()"
      end
  | Ecall ("list", [Ecall ("range", [e1])]) ->
      let v1 = expr ctx e1 in
      begin match v1 with
        | Vint i ->
            let rec range n acc =
              if n == 0 then acc else range (n-1) (Vint (n-1) :: acc) in
            Vlist (range i [] |> Array.of_list)
        | _ -> error "unsupported operand types for len(range())"
      end
  | Ecall (f, el) ->
      let (arg, body) = Hashtbl.find functions f in
      let f_ctx = Hashtbl.create 16 in
      begin
        List.iter2 (fun id e -> Hashtbl.add f_ctx id (expr ctx e)) arg el;
        try begin stmt f_ctx body; Vnone end
        with Return (v) -> v
      end
  | Elist el ->
      Vlist (List.map (fun e -> expr ctx e) el |> Array.of_list)
  | Eget (e1, e2) ->
      let v1 = expr ctx e1 in
      let v2 = expr ctx e2 in
      begin match v1, v2 with
        | Vlist l, Vint i -> Array.get l (vlist_idx l i)
        | _ -> error "unsupported operand types for l[i]"
      end

(* interpretation of an instruction; does not return anything *)

and stmt ctx = function
  | Seval e ->
      ignore (expr ctx e)
  | Sprint e ->
      print_value (expr ctx e); printf "@."
  | Sblock bl ->
      block ctx bl
  | Sif (e, s1, s2) ->
      if is_true (expr ctx e) then
        stmt ctx s1
      else
        stmt ctx s2
  | Sassign (id, e1) ->
      Hashtbl.add ctx id (expr ctx e1)
  | Sreturn e ->
      return (expr ctx e)
  | Sfor (x, e, s) ->
      let v = expr ctx e in
      begin match v with
        | Vlist l -> Array.iter (fun vv -> Hashtbl.add ctx x vv; stmt ctx s) l
        | _ -> error "unsupported operand types for loop"
      end
  | Sset (e1, e2, e3) ->
      let v1 = expr ctx e1 in
      let v2 = expr ctx e2 in
      begin match v1, v2 with
        | Vlist l, Vint i -> Array.set l (vlist_idx l i) (expr ctx e3)
        | _ -> error "unsupported operand types for l[i]="
      end

(* interpretation of a block i.e. of a sequence of instructions *)

and block ctx = function
  | [] -> ()
  | s :: sl -> stmt ctx s; block ctx sl

(* interpretation of a file
    - dl is a list of function definitions (see Ast.def)
    - s is an instruction, which represents the global instructions
 *)

let file (dl, s) =
  List.iter (fun (id, arg, body) -> Hashtbl.add functions id (arg, body)) dl;
  stmt (Hashtbl.create 16) s

