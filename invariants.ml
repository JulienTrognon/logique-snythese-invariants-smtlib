open Printf

(* Définitions de terme, test et programme *)

type term =
 | Const of int
 | Var of int
 | Add of term * term
 | Mult of term * term

type test =
 | Equals of term * term
 | GreaterThan of term * term

let tt = Equals (Const 0, Const 0)
let ff = GreaterThan (Const 0, Const 0)

type program = {nvars : int;
                inits : int list;
                mods : term list;
                loopcond : test;
                assertion : test}

let x n = "x" ^ string_of_int n

(* Question 1. Écrire des fonctions `str_of_term : term -> string`
   et `str_of_test : test -> string` qui convertissent des termes
   et des tests en chaînes de caractères du format SMT-LIB.

  Par exemple, str_of_term (Var 3) retourne "x3", str_of_term (Add
   (Var 1, Const 3)) retourne "(+ x1 3)" et str_of_test (Equals (Var
   2, Const 2)) retourne "(= x2 2)". 
*)

(* convertit un term en string *)
let rec str_of_term (t : term) : string = 
  match t with 
  | Const c      -> string_of_int c (* 5 -> "5" *)
  | Var v        -> x v (* 4 -> "x4" *)
  | Add  (x1,x2) -> (* Add(3,4) -> "(+ 3 4)" *)
    "(+ " ^ (str_of_term x1) ^ " " ^ (str_of_term x2) ^ ")"
  | Mult (x1,x2) -> (* Mult(3,4) -> "(\* 3 4)" *)
    "(* " ^ (str_of_term x1) ^ " " ^ (str_of_term x2) ^ ")"
;;

(* convertit un test en string *)
let str_of_test (t : test) : string = 
  match t with
  | Equals      (x1,x2) -> (*Equals (3, 3) -> "(= 3 3)" *)
    "(= " ^ (str_of_term x1) ^ " " ^ (str_of_term x2) ^ ")"
  | GreaterThan (x1,x2) -> (*Equals (5, 3) -> "(> 5 3)" *)
    "(> " ^ (str_of_term x1) ^ " " ^ (str_of_term x2) ^ ")"
;;

let string_repeat s n =
  Array.fold_left (^) "" (Array.make n s)

(* Question 2. Écrire une fonction `str_condition : term list -> string`
   qui prend une liste de termes t1, ..., tk et retourne une chaîne
   de caractères qui exprime que le tuple (t1, ..., tk) est dans
   l'invariant.  Par exemple, str_condition [Var 1; Const 10] retourne
   "(Invar x1 10)". 
*)

(* convertit une liste de termes en une chaine (Invar t1 .. tn) *)
let str_condition (l : term list) : string  = 
  let rec aux (lst : term list) (str : string) : string =
    match lst with
    | []     -> str (* condition d'arret *)
    | hd::tl -> aux tl (str ^ " " ^ (str_of_term hd)) (* ajoute à la suite chaque terme *)
  in "(Invar" ^ (aux l "") ^ ")"
;;

(* Question 3. Écrire une fonction
   `str_assert_for_all : int -> string -> string` qui prend en
   argument un entier n et une chaîne de caractères s, et retourne
   l'expression SMT-LIB qui correspond à la formule "forall x1 ... xk
   (s)".

  Par exemple, str_assert_forall 2 "> x1 x2" retourne : "(assert
   (forall ((x1 Int) (x2 Int)) (> x1 x2)))".  
*)

let str_assert s = "(assert " ^ s ^ ")"

let str_assert_forall (n : int) (s : string) : string = 
  let rec aux (i : int) : string = (* décrémente i, puis en faisant (n-i+1) cela ajoute dans l'odre croissant *)
    if i <= 0 then ""
    else if i = 1 then "(x" ^ (string_of_int n) ^ " Int)" (* condition d'arret *) (* meme chose que dans le else sans le trailing space *)
    else "(x" ^ (string_of_int (n-i+1)) ^ " Int) " ^ aux (i-1) (* construit la chaine des variables *)
  in str_assert ("(forall (" ^ (aux n) ^ ") (" ^ s ^ "))") (* chaine finale avec s entre parenthèses à la fin *)
;;

(* Question 4. Nous donnons ci-dessous une définition possible de la
   fonction smt_lib_of_wa. Complétez-la en écrivant les définitions de
   loop_condition et assertion_condition. *)

(* Renvoie une liste de termes composées de x1 x2 ... xn *)
let rec varlst (n : int) : (term list) = 
  let rec aux l i =
    if i <= 0 then l (* condition d'arret *)
    else (Var (n-i+1)) :: (aux l (i-1)) (* on ajoute x1, puis x2 etc *)
  in aux [] n
;;

let smtlib_of_wa p =
  let declare_invariant =
    "; synthèse d'invariant de programme\n"
    ^ "; on déclare le symbole non interprété de relation Invar\n"
    ^ "(declare-fun Invar (" ^ string_repeat "Int " p.nvars ^  ") Bool)" in

  let loop_condition =
    "; la relation Invar est un invariant de boucle\n"
    (* (str_condition (varlst p.nvars)) transforme l'info qu'il y a n variables 
       en "(Invar x1 x2 ... xn)" *)
    ^ str_assert_forall p.nvars ("=> (and " ^ (str_condition (varlst p.nvars))
    ^ " " ^ (str_of_test p.loopcond) ^ ") " 
    ^ str_condition p.mods) in

  let initial_condition =
    "; la relation Invar est vraie initialement\n"
    ^ str_assert (str_condition (List.map (function i -> Const i) p.inits)) in

  let assertion_condition =
    "; l'assertion finale est vérifiée\n"
    ^ str_assert_forall p.nvars ("=> (and " ^ (str_condition (varlst p.nvars)) 
    ^ " (not" ^ (str_of_test p.loopcond) ^ ")) " 
    ^ (str_of_test p.assertion)) in

  let call_solver =
    "; appel au solveur\n(check-sat-using (then qe smt))\n(get-model)\n(exit)\n" in
  String.concat "\n" [declare_invariant;
                      loop_condition;
                      initial_condition;
                      assertion_condition;
                      call_solver]

let p1 = {nvars = 2;
          inits = [4 ; 0];
          mods = [Add ((Var 1), (Const (-1))); Add ((Var 2), (Var 1))];
          loopcond = GreaterThan ((Var 1), (Const 0));
          assertion = Equals ((Var 2),(Const 10))}

(* Question 5. Vérifiez que votre implémentation donne un fichier
   SMT-LIB qui est équivalent au fichier que vous avez écrit à la main
   dans l'exercice 1. *)

let () = Printf.printf "p1:\n %s\n" (smtlib_of_wa p1)

(* Ajoutez dans la variable p2 ci-dessous au moins un autre programme
   test avec **trois** variables et vérifiez qu'il donne un fichier
   SMT-LIB la forme attendue. *)


 (* Programme en c correspondant à p2 :
  int x1 = 1, x2 = 3, x3 = 9;
  while (x3 > x2) {
    x1 = x1 + 1;
    x2 = x2 * x1;
    x3 = x3 + x1;
  }
  assert(x2 == x3 + x1 + 1);  *)

let p2 = {
  nvars = 3;
  inits = [1 ; 3 ; 9];
  mods = [
    Add  ((Var 1), (Const (1))); 
    Mult ((Var 2), (Var 1));
    Add  ((Var 3), (Var (1)))
  ];
  loopcond = GreaterThan ((Var 3), (Var 2));
  assertion = GreaterThan (Add((Var 3),(Var 1)), (Var 2))
}

let () = Printf.printf "p2:\n%s" (smtlib_of_wa p2)
