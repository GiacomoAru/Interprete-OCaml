type ide = string;;

	(*Ambiente*)
type 'v env = (string * 'v) list;;

	(*Introduzione di valori di tipo per il typechecker esteso agli insiemi*)
type tp = TInt
        | TBool
        | TString
        | TClosure 
        | TRecClosure
        | TSet of tp 	(*tipo (ricorsivo) specifico insiemi*)
        | TGenericSet 	(*tipo generico insiemi*) 
        | TVoid
;;

type exp = CstInt of int
         | CstTrue 
         | CstFalse 
         | Den of ide
         | Sum of exp * exp
         | Sub of exp * exp
         | Times of exp * exp
         | Ifthenelse of exp * exp * exp
         | Eq of exp * exp
         | Let of ide * exp * exp
         | Fun of ide * exp
         | Letrec of ide * ide * exp * exp
         | Apply of exp * exp

			(*Stringhe, espressione nulla e operazioni su interi e booleani utili*)
         | CstString of string
         | Succ of exp
         | Prec of exp
         | And of exp * exp
         | Or of exp * exp

			(*Espressioni per Set*) 
			(*Creatori base*) 
         | Empty of tp
         | Singleton of exp 
         | Of of exp list
             
			(*Operazioni base*) 
         | UnionSet of exp * exp
         | InterSet of exp * exp
         | DiffSet of exp * exp

			(*Insert, remove e operazioni di controllo per insiemi*) 
         | Insert of exp * exp
         | Remove of exp * exp
         | IsEmpty of exp
         | Contains of exp * exp
         | SubSet of exp * exp

			(*Max e Min, non definite su insiemi vuoti*) 
         | Min of exp
         | Max of exp

			(*Espressioni per applicare funzioni a elementi dei set*) 	
         | Decapitate of exp			(*Elimina l'elemento più piccolo dell'insieme, se esiste*)
         | ApplyFirst of exp * exp		(*Applica una funzione al più piccolo elemento dell'insieme e poi restituisce 						il risultato*)

			(*Operazioni complesse su insiemi richieste dal progetto*) 
         | ForAll of exp * exp
         | Exist of exp * exp
         | Map of exp * exp 
         | Filter of exp * exp
;;

type evT = Int of int 
         | Bool of bool 
         | Closure of ide * exp * evT env 
         | RecClosure of ide * ide * exp * evT env 
         | Unbound 
         | String of string

		(*nell'ambiente un set è una coppia (tipo, lista di valori dell'ambiente del tipo indicato)*) 
         | Set of tp * ( evT list )
;;


	(*bind generalizzato e lookup*) 
let bind s (i:string) x = ( i, x ) :: s;;

let rec lookup (s:evT env) (i:string) = match s with
  | [] ->  Unbound
  | (j,v)::sl when j = i -> v
  | _::sl -> lookup sl i;;


	(*Funzioni di supporto per il typecheck*)

	(*predne evT e restituisce tp corrispondente*)
let get_tp_evT (x:evT) = match x with
    Int(n) -> TInt
  | String(s) -> TString
  | Bool(b) -> TBool
  | Closure(_,_,_) -> TClosure
  | RecClosure(_,_,_,_) -> TRecClosure
  | Set(t,_) ->  TSet(t)
  | _ -> failwith("runtime error")
;; 

let typecheck ((x:tp), (y:evT)) = match x with	
  | TInt -> (match y with 
        Int(u) -> true
      | _ -> false)
  | TBool -> (match y with 
        Bool(u) -> true
      | _ -> false)
		(*Novità*)
  | TString -> (match y with
        String(u) -> true
      | _ -> false)
  | TClosure -> (match y with
        Closure(_,_,_) -> true
      | _ -> false)
  | TRecClosure -> (match y with
        RecClosure(_,_,_,_) -> true
      | _ -> false)	
  | TSet(t) -> (match y with
        Set(r,_) -> r = t
      | _ -> false)	
  | TGenericSet  -> (match y with
        Set(_,_) -> true
      | _ -> false)	
  | TVoid -> false
;;


	(*Inizialmente ho valutato la possibilità di usare la ricerca binaria per
	operare sui Set ma questo andava in conflitto con l'operando @ di complessità O(n), 
	con la rappresentazione delle liste in caml e il non avere un accesso diretto stile 
	array(almeno nelle librerie standard). Perciò mi sono accontentato di una 
	ricerca sequenziale su liste ordinate*)

	(*Funzioni ausiliarie per la valutazione di espressioni*)

	(*Una possibile scelta di implementazione utile per massimizzare il riutilizzo dello stesso codice
	ma che non porta migliorie in tempo di esecuzione*) 
(*let rec ordered_list_find p l1 = match l1 with
      [] -> ([], [], [])
    | uno::due -> if p(uno) then ([], [uno], due)
        else let (a,b,c) = ordered_list_find p due in
          (uno::a, b, c)
 ;;
let find_and_add_2 l1 el = 
   match ordered_list_find (fun x -> x >= el) l1 with
     ([], [], []) -> [el]
   | (d, [e], f) -> if e = el then l1
       else d@[el]@[e]@f;;	
 ;;*)


let rec find_and_add l1 el = match l1 with
    [] -> [el]
  |	uno::due -> if uno < el then uno::(find_and_add due el)
      else if uno = el then uno::due
      else el::uno::due
;;
let rec find_and_remove l1 el = match l1 with
    [] -> []
  |	uno::due -> if uno < el then uno::(find_and_remove due el)
      else if uno = el then due
      else uno::due
;;
let rec ordered_list_union l1 l2 = match l1 with
    [] -> l2
  | uno::due ->( match l2 with 
        [] -> l1
      | tre::quattro -> if(uno < tre) then uno::(ordered_list_union due (tre::quattro))
          else if (uno = tre) then uno::(ordered_list_union due quattro)
          else tre::(ordered_list_union (uno::due) quattro)
    )
;;
let rec ordered_list_intersection l1 l2 = match l1 with
    [] -> []
  | uno::due ->( match l2 with 
        [] -> []
      | tre::quattro -> if(uno < tre) then (ordered_list_intersection due (tre::quattro))
          else if (uno = tre) then uno::(ordered_list_intersection due quattro)
          else ordered_list_intersection (uno::due) quattro
    )
;;

	(*Rimuove gli elementi di l2 in l1*)
let rec ordered_list_difference l1 l2 = match l1 with 
    [] -> []
  | uno::due ->( match l2 with 
        [] -> l1
      | tre::quattro -> if(uno < tre) then uno::(ordered_list_difference due (tre::quattro))
          else if (uno = tre) then ordered_list_difference due quattro
          else ordered_list_difference (uno::due) quattro
    )
;;
let rec ordered_list_contains l1 el = match l1 with
    [] -> Bool(false)
  | uno::due -> if uno < el then ordered_list_contains due el
      else if uno = el then Bool(true)
      else Bool(false);;

	(*Controlla se l1 è sottoinsieme di l2*)
let rec ordered_list_subSet l1 l2 = match l1 with
    [] -> Bool(true)
  | uno::due -> ( match l2 with
        [] -> Bool(false)
      | tre::quattro -> if uno < tre then Bool(false)
          else if uno = tre then ordered_list_subSet due quattro
          else ordered_list_subSet (uno::due) quattro );;
let rec ordered_list_max l1 = match l1 with
    [] -> Unbound
  | uno::[] -> uno
  | uno::due::tre -> ordered_list_max (due::tre);;
let ordered_list_min l1 = match l1 with
    [] -> Unbound
  | uno::due -> uno;; 


	(*Interprete e typechecker per operazioni su valori base*)

let int_eq(x,y) =   
  match (typecheck(TInt,x), typecheck(TInt,y), x, y) with
  | (true, true, Int(v), Int(w)) -> Bool(v = w)
  | (_,_,_,_) -> failwith("run-time error");;
       
let int_plus(x, y) = 
  match(typecheck(TInt,x), typecheck(TInt,y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v + w)
  | (_,_,_,_) -> failwith("run-time error");;

let int_sub(x, y) = 
  match(typecheck(TInt,x), typecheck(TInt,y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v - w)
  | (_,_,_,_) -> failwith("run-time error");;

let int_times(x, y) = 
  match(typecheck(TInt,x), typecheck(TInt,y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v * w)
  | (_,_,_,_) -> failwith("run-time error");;


	(*Novità*)
let int_succ x = match( typecheck(TInt, x), x) with
  | (true, Int(v)) -> Int(v + 1)
  | (_,_) -> failwith("run-time error");;

let int_prec x = match( typecheck(TInt, x), x) with
  | (true, Int(v)) -> Int(v - 1)
  | (_,_) -> failwith("run-time error");;

let bool_and (x,y) = match (typecheck(TBool,x), typecheck(TBool,y), x, y) with
  | (true, true, Bool(v), Bool(w)) -> Bool(v && w)
  | (_,_,_,_) -> failwith("run-time error");;
let bool_or (x,y) = match (typecheck(TBool,x), typecheck(TBool,y), x, y) with
  | (true, true, Bool(v), Bool(w)) -> Bool(v || w)
  | (_,_,_,_) -> failwith("run-time error");;


	(*Interprete e typechecker per operazioni su insiemi*)

let set_union(x, y) = 
  match( typecheck(get_tp_evT x , y), typecheck(TGenericSet,x), x, y) with
    (true, true, Set(uno, due), Set(tre, quattro)) ->
      Set( uno, (ordered_list_union due quattro))
  | (_,_,_,_) -> failwith("run-time error");;
let set_intersection(x, y) = 
  match( typecheck(get_tp_evT x , y), typecheck(TGenericSet,x), x, y) with
    (true, true, Set(uno, due), Set(tre, quattro)) ->
      Set( uno, (ordered_list_intersection due quattro))
  | (_,_,_,_) -> failwith("run-time error");;
let set_difference(x, y) = 
  match( typecheck(get_tp_evT x , y), typecheck(TGenericSet,x), x, y) with
    (true, true, Set(uno, due), Set(tre, quattro)) ->
      Set( uno, (ordered_list_difference due quattro))
  | (_,_,_,_) -> failwith("run-time error");;
let set_isEmpty (x) = 
  match ( typecheck(TGenericSet, x), x) with
    (true, Set(uno, due)) ->( match due with
        [] -> Bool(true)
      | _ -> Bool(false) )
  | (_,_) -> failwith("run-time error");;
let set_contains (x , y) = 
  match x with
    Set(uno, due) ->( if typecheck(uno, y) then ordered_list_contains due y 
                      else failwith("run-time error")	)
  | _ -> failwith("run-time error")
;;
let set_subSet (x, y) = 
  match (typecheck(get_tp_evT x, y), typecheck(TGenericSet, x) , x, y) with 
    (true, true, Set(uno, due), Set(tre, quattro) ) -> ordered_list_subSet due quattro
  | (_,_,_,_) -> failwith("run-time error");;
let set_max x = 
  match (typecheck(TGenericSet, x), x) with
    (true, Set(uno, due::tre)) -> ordered_list_max (due::tre)
  | (_,_) -> failwith("run-time error");;
let set_min x = 
  match (typecheck(TGenericSet, x), x) with
    (true, Set(uno, due::tre)) -> ordered_list_min (due::tre)
  | (_,_) -> failwith("run-time error");;
let set_decapitate x =
  match (typecheck(TGenericSet, x), x) with
    (true, Set(uno, due::tre)) -> Set(uno, tre)
  | (true, Set(uno, [])) -> Set(uno, []) (*decapitate di insieme vuoto restituisce l'insieme stesso*)
  | (_,_) -> failwith("run-time error");;


	(*Interprete generale*)

let rec eval  (e:exp) (s:evT env) = match e with
    CstInt(n) -> Int(n)
  | CstTrue -> Bool(true)
  | CstFalse -> Bool(false) 
  | Eq(e1, e2) -> int_eq((eval e1 s), (eval e2 s))
  | Times(e1,e2) -> int_times((eval e1 s), (eval e2 s))
  | Sum(e1, e2) -> int_plus((eval e1 s), (eval e2 s))
  | Sub(e1, e2) -> int_sub((eval e1 s), (eval e2 s))
  | Ifthenelse(e1,e2,e3) -> let g = eval e1 s in
      (match (typecheck(TBool, g), g) with
       | (true, Bool(true)) -> eval e2 s
       | (true, Bool(false)) -> eval e3 s
       | (_, _) -> failwith ("nonboolean guard"))
  | Den(i) -> lookup s i
  | Let(i, e1, ebody) -> eval ebody (bind s i (eval e1 s))
  | Fun(arg, ebody) -> Closure(arg,ebody,s)
  | Letrec(f, arg, fBody, letBody) -> 
      let benv = bind (s) (f) (RecClosure(f, arg, fBody,s)) in
      eval letBody benv
  | Apply(eF, eArg) ->
      let fclosure = eval eF s in 
      (match fclosure with 
       | Closure(arg, fbody, fDecEnv) ->
           let aVal = eval eArg s in
           let aenv = bind fDecEnv arg aVal in 
           eval fbody aenv
       | RecClosure(f, arg, fbody, fDecEnv) ->
           let aVal = eval eArg s in
           let rEnv = bind fDecEnv f fclosure in
           let aenv = bind rEnv arg aVal in 
           eval fbody aenv
       | _ -> failwith("non functional value"))


	(*Novità*)
  | CstString(str) -> String(str)
  | Succ(e1) -> int_succ( eval e1 s )
  | Prec(e1) -> int_prec( eval e1 s )
  | And(e1, e2) -> bool_and( eval e1 s, eval e2 s)
  | Or(e1, e2) -> bool_or( eval e1 s, eval e2 s)


	(*Novità Progettose*)
  | Empty(t) -> Set(t, [])
  | Singleton(e1) -> let v = eval e1 s in Set( (get_tp_evT v) , [v]) 
  | Of(l) ->( match l with 
        [] -> failwith("parameter must contain at least one element")
      | [uno] -> eval (Singleton(uno)) s
      | uno::due::tre -> eval (Insert(Of(due::tre), uno)) s
    )

  | Insert(eSet, e1) ->(let vSet = eval eSet s in 
                        let v1 = eval e1 s in 
                        match vSet with
                          Set(TVoid, []) -> Set((get_tp_evT v1), [v1])
                        | Set(t, lst) -> ( match typecheck(t, v1) with
                              true -> Set(t, (find_and_add lst v1)) 
                            | _ ->  failwith("Type error"))

                        | _ -> failwith("Type error") )
  | Remove(eSet, e1) ->(match eval eSet s with
        Set(t, lst) -> let vl = eval e1 s in if typecheck(t, vl) 
          then (let dummy = find_and_remove lst vl in Set(t, dummy)) 
          else failwith("Type error") 
              
      | _ -> failwith("type error") )

  | IsEmpty(eSet) -> set_isEmpty( eval eSet s )
  | Contains(eSet, e1) -> set_contains(eval eSet s, eval e1 s)
  | UnionSet(e1, e2) -> set_union( eval e1 s, eval e2 s)
  | InterSet(e1, e2) -> set_intersection( eval e1 s, eval e2 s)
  | DiffSet(e1, e2) -> set_difference( eval e1 s, eval e2 s)
  | SubSet(e1, e2) -> set_subSet(eval e1 s, eval e2 s)
  | Max(e1) -> set_max(eval e1 s)
  | Min(e1) -> set_min(eval e1 s)

  | Decapitate(e1) -> set_decapitate(eval e1 s) 
  | ApplyFirst(eF, eSet) -> let fclosure = eval eF s in 
      (match fclosure with 
       | Closure(arg, fbody, fDecEnv) ->
           let aVal = eval eSet s in (match aVal with
                 Set(uno, due::tre) -> (let aenv = bind fDecEnv arg due in eval fbody aenv)
               | _ -> failwith("type error"))

       | RecClosure(f, arg, fbody, fDecEnv) ->
           let aVal = eval eSet s in
           let rEnv = bind fDecEnv f fclosure in (match aVal with
                 Set(uno, due::tre) -> (let aenv = bind rEnv arg due in eval fbody aenv)
               | _ -> failwith("type error"))
       | _ -> failwith("non functional value"))

  | ForAll(eF, eSet) -> ( match (eval eSet s) with
        Set(uno, []) -> Bool(true)
      | Set(uno, due::tre) -> eval (And( (ApplyFirst( (eF),(eSet) )), ( ForAll( (eF),(Decapitate(eSet)) ) ) )) s
      | _ -> failwith("type error") )
  | Exist(eF, eSet) -> ( match (eval eSet s) with
        Set(uno, []) -> Bool(false)
      | Set(uno, due::tre) -> eval (Or( (ApplyFirst( (eF),(eSet) )), ( Exist( (eF),(Decapitate(eSet)) ) ) )) s
      | _ -> failwith("type error") )
  | Map(eF, eSet) -> ( match (eval eSet s) with
        Set(uno, []) -> Set(TVoid, [])  
      | Set(uno, due::quattro) -> eval (Insert( ( Map( (eF),(Decapitate(eSet)) ) )  , (ApplyFirst( (eF),(eSet) )))) s   
      | _ -> failwith("type error") )
  | Filter(eF, eSet) ->if (eval (IsEmpty(eSet)) s) = Bool(true) then eval eSet s
      else (match eval (ApplyFirst(eF,eSet)) s with
            Bool(true) -> eval (Insert( (Filter(eF, (Decapitate(eSet))))  , (Min(eSet)))) s
          | Bool(false) -> eval (Filter(eF, (Decapitate(eSet)))) s
          | _ -> failwith("type error") )

;; 

let (emptyEnv: evT env)  = [ ("", Unbound)] ;;
let eIntC = Let( ("var1"),(CstInt(10)),
                 (Let( ("FunC"),(Fun( ("var2"),(Times( (Den("var1")),(Den("var2")) )) )),
                       ( Let( ("var1"),(CstTrue),
                              (Apply( (Den("FunC")),(CstInt(3)) )) ) ) ) ) );;
let fact = Letrec( "fact", "x", 
                   (Ifthenelse( (Eq( (Den("x")),(CstInt(0)) )),
                                ( CstInt(1)),
                                ( Times( (Den("x")), (Apply( (Den("fact")),(Sub( (Den("x")),(CstInt(1)) )) )) )))), 
                   (Apply( (Den("fact")),(CstInt(5)) )));; 
let times2 = Fun( ("arg"),( Times( (Den("arg")),(CstInt(2)) ) ) );;
let ins1 = Of([CstInt(2);CstInt(53);CstInt(69);CstInt(23);CstInt(0);CstInt(-1);CstInt(700)]);;
let ins2 = Of([CstInt(0);CstInt(700)]);;
let ins3 = Of([CstInt(1);CstInt(99);CstInt(2);CstInt(69);CstInt(25);CstInt(36)]);;
let predicate = Fun( ("ide") , (Or( (Eq( (Den("ide")),(CstInt(2)))),
                                    (Eq( (Den("ide")),(CstInt(1)))) )));;

eval (Sum( (CstInt(9)),(CstInt(1)) )) emptyEnv;;
eval (Sub( (CstInt(9)),(CstInt(1)) )) emptyEnv;;
eval (Times( (CstInt(9)),(CstInt(2)) )) emptyEnv;;

eval (Let( ("id"),(CstTrue),
           ( Ifthenelse( (Den("id")),(Succ(CstInt(1))),(Prec(CstInt(1))) ) ) )) emptyEnv;; 
eval (Ifthenelse( (Eq( (CstInt(9)),(CstInt(3)) )),(Succ(CstInt(1))),(Prec(CstInt(1))) )) emptyEnv;; 

eval (And( (CstTrue),(CstFalse) )) emptyEnv;;
eval (Or( (CstTrue),(CstFalse) )) emptyEnv;;

eval (Insert( ( Of([Empty(TInt); Singleton(CstInt(8))]) ) , ( Singleton(CstInt(4))) )) emptyEnv;;
eval (UnionSet( (ins1),(ins3) ) ) emptyEnv;;
eval (InterSet( (ins1),(ins2) ) ) emptyEnv;; 
eval (DiffSet( (ins1),(ins2) )) emptyEnv;;
eval (Remove( (ins2),(CstInt(700)) )) emptyEnv;; 

eval (IsEmpty(Empty(TSet(TInt)))) emptyEnv;;
eval (Contains((ins3),(CstInt(25)))) emptyEnv;;
eval (SubSet((ins2),(ins1))) emptyEnv;;

eval (Max((Of([CstInt(88); CstInt(69); CstInt(88787); CstInt(-5)])))) emptyEnv;;
eval (Min((Of([CstInt(66); CstInt(8); CstInt(88787); CstInt(-5)])))) emptyEnv;; 

eval predicate emptyEnv;;
eval (Decapitate(ins1)) emptyEnv;;

eval (ApplyFirst( (predicate),(ins3) )) emptyEnv;;
eval (ApplyFirst( (predicate),(ins2) )) emptyEnv;;
eval (ForAll( (predicate),(ins3) )) emptyEnv;;
eval (Exist( (predicate),(ins3) )) emptyEnv;;
  
eval (Map( (times2),(ins1) )) emptyEnv;; 
eval (Filter( (predicate),(ins3) )) emptyEnv;;

eval fact emptyEnv;; 
eval eIntC emptyEnv;;





