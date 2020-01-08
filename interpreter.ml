(* expressions *)

type ide = string;;

type exp =
    Eint of int
  | Ebool of bool
  | Den of ide
  | Prod of exp * exp
  | Sum of exp * exp
  | Diff of exp * exp
  | Eq of exp * exp
  | Minus of exp
  | IsZero of exp
  | Or of exp * exp
  | And of exp * exp
  | Not of exp
  | Ifthenelse of exp * exp * exp
  | Let of ide * exp * exp
  | Fun of ide * exp
  | FunCall of exp * exp
  | Letrec of ide * exp * exp
  | Estring of string
  | Dict of (ide * exp) list
  | Insert of ide * exp * exp
  | Delete of exp * ide
  | HasKey of ide * exp
  | Iterate of exp * exp
  | Fold of exp * exp
  | Filter of ide list * exp;;


(* environment *)

type 't env = ide -> 't;;

let emptyenv (v: 't) = function x -> v;;

let applyenv (r : 't env) (i : ide) = r i;;

let bind (r : 't env) (i : ide) (v : 't) =
  function x -> if x = i then v
                         else applyenv r x;;


(* expressible values *)

type evT =
    Int of int
  | Bool of bool
  | String of string
  | Unbound
  | FunVal of evFun
  | RecFunVal of ide * evFun
  | Valdict of (ide * evT) list
  and evFun = ide * exp * evT env;;


(* runtime support *)

(* type checking *)

let typecheck (s : string) (v : evT) : bool =
  match s with
  | "int" -> (match v with
              | Int(_) -> true
              | _ -> false)
  | "bool" -> (match v with
               | Bool(_) -> true
               | _ -> false)
  | _ -> failwith("not a valid type");;


(* primitive functions *)

let prod x y =
  if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        | (Int(n),Int(u)) -> Int(n*u)
        | _ -> failwith("error in applying function"))
  else failwith("Type error");;

let sum x y =
  if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        | (Int(n),Int(u)) -> Int(n+u)
        | _ -> failwith("error in applying function"))
  else failwith("Type error");;

let diff x y =
  if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        | (Int(n),Int(u)) -> Int(n-u)
        | _ -> failwith("error in applying function"))
  else failwith("Type error");;

let eq x y =
  if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
        | (Int(n),Int(u)) -> Bool(n=u)
        | _ -> failwith("error in applying function"))
  else failwith("Type error");;

let minus x =
  if (typecheck "int" x)
  then (match x with
        | Int(n) -> Int(-n)
        | _ -> failwith("error in applying function"))
  else failwith("Type error");;

let iszero x =
  if (typecheck "int" x)
  then (match x with
        | Int(n) -> Bool(n=0)
        | _ -> failwith("error in applying function"))
  else failwith("Type error");;

let vel x y =
  if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
        | (Bool(b),Bool(e)) -> (Bool(b||e))
        | _ -> failwith("error in applying function"))
  else failwith("Type error");;

let et x y =
  if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
        | (Bool(b),Bool(e)) -> Bool(b&&e)
        | _ -> failwith("error in applying function"))
  else failwith("Type error");;

let non x =
  if (typecheck "bool" x)
  then (match x with
        | Bool(true) -> Bool(false)
        | Bool(false) -> Bool(true)
        | _ -> failwith("Type error"))
  else failwith("Type error");;


(* interpreter *)

let rec eval (e : exp) (r : evT env) : evT =
  match e with
  | Eint n -> Int n
  | Ebool b -> Bool b
  | IsZero a -> iszero (eval a r)
  | Den i -> applyenv r i
  | Eq(a, b) -> eq (eval a r) (eval b r)
  | Prod(a, b) -> prod (eval a r) (eval b r)
  | Sum(a, b) -> sum (eval a r) (eval b r)
  | Diff(a, b) -> diff (eval a r) (eval b r)
  | Minus a -> minus (eval a r)
  | And(a, b) -> et (eval a r) (eval b r)
  | Or(a, b) -> vel (eval a r) (eval b r)
  | Not a -> non (eval a r)
  | Ifthenelse(a, b, c) ->
      let g = (eval a r) in
        if (typecheck "bool" g) then (if g = Bool(true) then (eval b r) else (eval c r))
                                else failwith ("non boolean guard")
  | Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r))
  | Fun(i, a) -> FunVal(i, a, r)
  | FunCall(f, eArg) ->
      let fClosure = (eval f r) in
        (match fClosure with
         | FunVal(arg, fBody, fDecEnv) -> eval fBody (bind fDecEnv arg (eval eArg r))
         (* in order to obtain static scope the function has to be evaluated with its declaration environment 'fDecEnv';
            to obtain dynamic scope the function has to be evaluated with the current environment 'r' *)
         | RecFunVal(g, (arg, fBody, fDecEnv)) ->
             let aVal = (eval eArg r) in
               let rEnv = (bind fDecEnv g fClosure) in
                 let aEnv = (bind rEnv arg aVal) in
                   eval fBody aEnv
         | _ -> failwith("non functional value"))
  | Letrec(f, funDef, letBody) ->
      (match funDef with
        | Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in eval letBody r1
        | _ -> failwith("non functional def"))
  | Estring s -> String s
  | Dict(list) ->
      (* returns the list of (key, exp) with every pair evaluated (key, value) *)
      let rec evalist (l : (ide * exp) list) (r : evT env) : (ide * evT) list =
        match l with
        | [] -> []
        | (k1, v1)::t -> (k1, eval v1 r)::(evalist t r)
      in Valdict(evalist list r)
  | Insert(key, value, dict) ->
      (match eval dict r with
      | Valdict v ->
          (* if the key isn't already present, returns a new dictionary in wich is added the element (key, value) *)
          let rec insert (key : ide) (value : evT) (dict : (ide * evT) list) : (ide * evT) list =
            match dict with
            | [] -> (key, value)::[]
            | (k1, v1)::t -> if (key = k1) then (k1, v1)::t else (k1, v1)::(insert key value t)
          in Valdict(insert key (eval value r) v)
      | _ -> failwith("not a dictionary"))
  | Delete(dict, key) ->
      (match eval dict r with
      | Valdict v ->
          (* if the key is present, returns a new dictionary in wich is removed the element (key, _) *)
          let rec delete (key : ide) (dict : (ide * evT) list) : (ide * evT) list =
            match dict with
            | [] -> []
            | (k1, v1)::t -> if (key = k1) then t else (k1, v1)::(delete key t)
          in Valdict(delete key v)
      | _ -> failwith("not a dictionary"))
  | HasKey(key, dict) ->
      (match eval dict r with
      | Valdict v ->
          (* if the key is present in the dictionary returns true, else false *)
          let rec contains (key : ide) (dict : (ide * evT) list) : bool =
            match dict with
            | [] -> false
            | (k1, _)::t -> if (key = k1) then true else contains key t
          in Bool(contains key v)
      | _ -> failwith("not a dictionary"))
  | Iterate(funct, dict) ->
      (match eval funct r, dict with
      | FunVal(_, _, _), Dict v ->
          (* returns a new dictionary in wich the function f has been applied to each element *)
          let rec apply (f : exp) (dict : (ide * exp) list) (r : evT env) : (ide * evT) list =
            match dict with
            | [] -> []
            | (k1, v1)::t -> (k1, eval (FunCall(f, v1)) r)::(apply f t r)
          in Valdict(apply funct v r)
      | _ -> failwith("not a dictionary"))
  | Fold(funct, dict) ->
      (match eval funct r, dict with
      | FunVal(_, _, _), Dict v ->
          (* applies the function f to each int value of the dictionary dict and returns the summation of every value *)
          let rec fold (f : exp) (dict : (ide * exp) list) (acc : evT) (r : evT env) : evT =
            match dict with
            | [] -> acc
            | (_, v1)::t -> match acc, (eval (FunCall(f, v1)) r) with
                            | (Int(u), Int(v)) -> fold f t (Int(u+v)) r
                            | _ -> failwith("error in applying function")
          in fold funct v (Int(0)) r
      | _ -> failwith("not a dictionary"))
  | Filter(keylist, dict) ->
      (match eval dict r with
      | Valdict v ->
          (* returns a subset of the dictionary dict containing the keys that are also contained in the list l *)
          let rec filter (l : ide list) (dict : (ide * evT) list) : (ide * evT) list =
            match dict with
            | [] -> []
            | (k1, v1)::t -> if (List.mem k1 l) then (k1, v1)::(filter l t) else filter l t
          in Valdict(filter keylist v)
      | _ -> failwith("not a dictionary"))
  ;;


(* =============================  TESTS  ================= *)

let env0 = emptyenv Unbound;;

let e1 = FunCall(Fun("y", Sum(Den "y", Eint 1)), Eint 3);;

eval e1 env0;;

let e2 = FunCall(Let("x", Eint 2, Fun("y", Sum(Den "y", Den "x"))), Eint 3);;

eval e2 env0;;

(* ======================================================= *)

(* declaring the empty env *)
let env0 = emptyenv Unbound;;

(* creating the fruit dictionary *)
let dict = Dict([("apple", Eint(567)); ("banana", Eint(86)); ("cherry", Eint(93)); ("kiwi", Eint(743)); ("mango", Eint(99))]);;

(* evaluating the dictionary in the current environment *)
eval dict env0;;

(* inserting the non-existing element ("orange", 10) in a new copy of the dictionary - EXPECTING SUCCESSFUL OUTCOME *)
eval (Insert("orange", Eint(10), dict)) env0;;
(* inserting the already-existing element ("orange", 10) in a new copy of the dictionary - EXPECTING UNSUCCESSFUL OUTCOME *)
eval (Insert("apple", Eint(54), dict)) env0;;

(* deleting the existing element ("banana", _) from a new copy of the dictionary - EXPECTING SUCCESSFULL OUTCOME *)
eval (Delete(dict, "banana")) env0;;
(* deleting the non-existing element ("notafruit", _) from a new copy of the dictionary - EXPECTING UNSUCCESSFUL OUTCOME *)
eval (Delete(dict, "notafruit")) env0;;

(* checking if the element ("apple", _) exists in the dictionary - EXPECTING TRUE*)
eval (HasKey("apple", dict)) env0;;
(* checking if the element ("notafruit", _) exists in the dictionary - EXPECTING FALSE *)
eval (HasKey("notafruit", dict)) env0;;

(* declaring the function f that takes a int value and returns its successor *)
let f = Fun("y", Sum(Den "y", Eint 1));;

(* applying the function f to each element of the dictionary and returning a new dictionary - EXPECTING SUCCESSFUL OUTCOME *)
eval (Iterate(f, dict)) env0;;

(* applying the function fold with the function f to each element of the dictionary - EXPECTING SUCCESSFUL OUTCOME *)
eval (Fold(f, dict)) env0;;

(* declaring a mask to filter the dictionary elements *)
let mask = ["cherry"; "kiwi"; "grape"];;

(* filtering the dictionary elements returning a new dictionary - EXPECTING SUCCESSFUL OUTCOME *)
eval (Filter(mask, dict)) env0;;
