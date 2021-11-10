type ide = string;;

type 'v env = (string * 'v) list;;

	(*Introduzione del tipo tp che deve restituire il typecheck*)
type tp = TInt
        | TBool
        | TString 
        | TSet of tp 	(*tipo (ricorsivo) specifico insiemi*) 
        | TVoid	(*tipo vuoto --> Unbound*)

        | STCClosure of tp * tp (*funzioni senza differenziazione tra ricorsive o non*)
;;

	(*Espressioni concesse dal nostro linguaggio*)
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
         | StaticTCFun of ide * tp * tp * exp 
         | StaticTCLetRec of ide * tp * ide * tp * exp * exp 
         | Apply of exp * exp
                    
			(*Aggiunte*)
         | CstString of string
         | Succ of exp
         | Prec of exp

			(*Aggiunte riguardanti il tipo di dato Set*) 
         | Empty of tp
         | Singleton of exp 
         | Of of exp list

         | UnionSet of exp * exp
         | InterSet of exp * exp
         | DiffSet of exp * exp

         | Insert of exp * exp
         | Remove of exp * exp
         | IsEmpty of exp
         | Contains of exp * exp
         | SubSet of exp * exp
         | Min of exp			(*Min e Max non sono definite su insiemi vuoti, generano errori*)
         | Max of exp

         | And of exp * exp
         | Or of exp * exp
         | Decapitate of exp		(*taglia il primo elemento dall'insieme, se c'è*)
         | ApplyFirst of exp * exp	(*applica la funzione primo parametro al primo elemento dell'insieme e restituisce
						il risultato*) 
         | ForAll of exp * exp		
         | Exist of exp * exp
         | Map of exp * exp 
         | Filter of exp * exp
;; 

	(*Funzione per fare e richiamare i binding nell'ambiente*)
let bind s (i:string) x = ( i, x ) :: s;; 
let rec lookupSTC s (i:string) = match s with
  | [] ->  TVoid
  | (j,v)::sl when j = i -> v
  | _::sl -> lookupSTC sl i;; 

	(*typechecker statico*)
let rec staticTC (e:exp) (s:tp env) = match e with 

	(*Valori primitivi e Den*)

  | CstInt(n) -> TInt
  | CstTrue -> TBool
  | CstFalse -> TBool
  | CstString(str) -> TString
  | Den(i) -> lookupSTC s i


	(*Espressioni su interi e booleani*)

  | Eq(e1, e2) ->( match (staticTC e1 s, staticTC e2 s) with
        (TInt, TInt) -> TBool
      | _ -> failwith("wrong type") )
  | Times(e1,e2) -> ( match (staticTC e1 s, staticTC e2 s) with
        (TInt, TInt) -> TInt
      | _ -> failwith("wrong type") )
  | Sum(e1, e2) -> ( match (staticTC e1 s, staticTC e2 s) with
        (TInt, TInt) -> TInt
      | _ -> failwith("wrong type") )
  | Sub(e1, e2) -> ( match (staticTC e1 s, staticTC e2 s) with
        (TInt, TInt) -> TInt
      | _ -> failwith("wrong type") )
  | Succ(e1) -> if (staticTC e1 s) = TInt then TInt else failwith("wrong type")
  | Prec(e1) -> if (staticTC e1 s) = TInt then TInt else failwith("wrong type")
  | And(e1, e2) ->( match (staticTC e1 s, staticTC e2 s) with
        (TBool, TBool) -> TBool
      | _ -> failwith("wrong type") )
  | Or(e1, e2) -> ( match (staticTC e1 s, staticTC e2 s) with
        (TBool, TBool) -> TBool
      | _ -> failwith("wrong type") )


	(*If then else*)

  | Ifthenelse(e1,e2,e3) -> ( match (staticTC e1 s, staticTC e2 s, staticTC e3 s) with
        (TBool, t1, t2) -> if t1 = t2 then t1
          else failwith("wrong type")
      | _ -> failwith("wrong type") )


	(*Let, creazione e applicazione di funzioni lambda*)

  | Let(i, e1, ebody) -> staticTC ebody (bind s i (staticTC e1 s))
  | StaticTCFun(arg, tpArg, tpOut, ebody) -> let tpO = staticTC ebody (bind s arg tpArg) in 
      if tpO = tpOut then STCClosure(tpArg, tpOut) else failwith("wrong type")
  | StaticTCLetRec(i1, tpIn, i2, tpOut, eFun, ebody) ->(
      let env1 = bind s i2 (STCClosure(tpIn, tpOut)) in
      let env2 = bind env1 i1 tpIn in 
      let tpCheck = staticTC eFun env2 in
      if tpCheck = tpOut then staticTC ebody (bind s i2 (STCClosure(tpIn, tpOut)))
      else failwith("wrogn type"))
  | Apply(eF, eArg) -> ( match (staticTC eF s, staticTC eArg s) with
        (STCClosure(a, b), c) -> if( c = a ) then b else failwith("wrong type")	
      | _ -> failwith("wrong type") ) 


	(*Operazioni su insiemi*)

  | Empty(t) -> TSet(t)	
  | Singleton(e1) -> let v = staticTC e1 s in TSet(v)
  | Of(l) ->( match l with 
        [] -> failwith("parameter must contain at least one element")
      | [uno] -> staticTC (Singleton(uno)) s
      | uno::due::tre -> staticTC (Insert(Of(due::tre), uno)) s
    )

  | Insert(eSet, e1) ->(match (staticTC eSet s, staticTC e1 s ) with
        (TSet(TVoid), b) -> TSet(b)
      | (TSet(a), b) -> if ( a = b) then TSet(a) else failwith("type error") 
      | _ -> failwith("type error") )
  | Remove(eSet, e1) ->(match (staticTC eSet s, staticTC e1 s ) with
        (TSet(a), b) -> if ( a = b ) then TSet(a) else failwith("type error")
      | _ -> failwith("type error"))

  | IsEmpty(eSet) ->(match staticTC eSet s with
        TSet(a) -> TBool
      | _ -> failwith("type error") )
  | Contains(eSet, e1) ->(match (staticTC eSet s, staticTC e1 s) with
        (TSet(a), b) -> if a = b then TBool else failwith("type error")
      | _ -> failwith("type error") )
  | UnionSet(e1, e2) ->(match (staticTC e1 s, staticTC e2 s) with
        (TSet(a), TSet(b)) -> if a = b then TSet(a) else failwith("type error")
      | _ -> failwith("type error") )
  | InterSet(e1, e2) ->(match (staticTC e1 s, staticTC e2 s) with
        (TSet(a), TSet(b)) -> if a = b then TSet(a) else failwith("type error")
      | _ -> failwith("type error") )
  | DiffSet(e1, e2) ->(match (staticTC e1 s, staticTC e2 s) with
        (TSet(a), TSet(b)) -> if a = b then TSet(a) else failwith("type error")
      | _ -> failwith("type error") )
  | SubSet(e1, e2) ->(match (staticTC e1 s, staticTC e2 s) with
        (TSet(a), TSet(b)) -> if a = b then TBool else failwith("type error")
      | _ -> failwith("type error") )
  | Max(eSet) ->(match staticTC eSet s with
        TSet(a) -> a
      | _ -> failwith("type error") )
  | Min(eSet) ->(match staticTC eSet s with
        TSet(a) -> a
      | _ -> failwith("type error") )
  | Decapitate(eSet) ->(match staticTC eSet s with
        TSet(a) ->  TSet(a)
      | _ -> failwith("type error") )
  | ApplyFirst(eF, eSet) -> ( match (staticTC eF s, staticTC eSet s) with
        (STCClosure(a, b), TSet(c)) -> if( a = c) then b else failwith("wrong type")	
      | _ -> failwith("wrong type") )

  | ForAll(eF, eSet) -> (match (staticTC eF s, staticTC eSet s) with
        (STCClosure(a, b), TSet(c)) -> if a = c then TBool else failwith("type error")
      | _ -> failwith("type error") )
  | Exist(eF, eSet) -> (match (staticTC eF s, staticTC eSet s) with
        (STCClosure(a, b), TSet(c)) -> if a = c then TBool else failwith("type error")
      | _ -> failwith("type error") )
  | Map(eF, eSet) ->(match (staticTC eF s, staticTC eSet s) with
        (STCClosure(a, b), TSet(c)) -> if a = c then TSet(b) else failwith("type error")
      | _ -> failwith("type error") )
  | Filter(eF, eSet) -> (match (staticTC eF s, staticTC eSet s) with
        (STCClosure(a, TBool), TSet(c)) -> if a = c then TSet(c) else failwith("type error")
      | _ -> failwith("type error") )
;;

let (emptyEnv: tp env)  = [ ("", TVoid)] ;;

let eIntC = Let( ("var1"),(CstInt(10)),
                 (Let( ("FunC"),(StaticTCFun( ("var2"),(TInt),(TInt),(Times( (Den("var1")),(Den("var2")) )) )),
                       ( Let( ("var1"),(CstTrue),
                              (Apply( (Den("FunC")),(CstInt(3)) )) ) ) ) ) );;

let fact = StaticTCLetRec( "x",(TInt), "fact", (TInt), 
                           (Ifthenelse( (Eq( (Den("x")),(CstInt(0)) )),
                                        ( CstInt(1)),
                                        ( Times( (Den("x")), (Apply( (Den("fact")),(Sub( (Den("x")),(CstInt(1)) )) )) )))), 
                           (Apply( (Den("fact")),(CstInt(5)) )));; 
let times2 = StaticTCFun( ("arg"), (TInt), (TInt),( Times( (Den("arg")),(CstInt(2)) ) ) );;
let ins1 = Of([CstInt(2);CstInt(53);CstInt(69);CstInt(23);CstInt(0);CstInt(-1);CstInt(700)]);;
let ins2 = Of([CstInt(0);CstInt(700)]);;
let ins3 = Of([CstInt(1);CstInt(99);CstInt(2);CstInt(69);CstInt(25);CstInt(36)]);;
let predicate = StaticTCFun( ("ide") ,(TInt),(TBool), (Or( (Eq( (Den("ide")),(CstInt(2)))),
                                                           (Eq( (Den("ide")),(CstInt(1)))) )));;

staticTC(Sum( (CstInt(9)),(CstInt(1)) )) emptyEnv;;
staticTC (Sub( (CstInt(9)),(CstInt(1)) )) emptyEnv;;
staticTC (Times( (CstInt(9)),(CstInt(2)) )) emptyEnv;;

staticTC (Let( ("id"),(CstTrue),
               ( Ifthenelse( (Den("id")),(Succ(CstInt(1))),(Prec(CstInt(1))) ) ) )) emptyEnv;; 
staticTC (Ifthenelse( (Eq( (CstInt(9)),(CstInt(3)) )),(Succ(CstInt(1))),(Prec(CstInt(1))) )) emptyEnv;; 

staticTC (And( (CstTrue),(CstFalse) )) emptyEnv;;
staticTC (Or( (CstTrue),(CstFalse) )) emptyEnv;;

staticTC (Insert( ( Of([Empty(TInt); Singleton(CstInt(8))]) ) , ( Singleton(CstInt(4))) )) emptyEnv;;
staticTC (UnionSet( (ins1),(ins3) ) ) emptyEnv;;
staticTC (InterSet( (ins1),(ins2) ) ) emptyEnv;; 
staticTC (DiffSet( (ins1),(ins2) )) emptyEnv;;
staticTC (Remove( (ins2),(CstInt(700)) )) emptyEnv;; 

staticTC (IsEmpty(Empty(TSet(TInt)))) emptyEnv;;
staticTC (Contains((ins3),(CstInt(25)))) emptyEnv;;
staticTC (SubSet((ins2),(ins1))) emptyEnv;;

staticTC (Max((Of([CstInt(88); CstInt(69); CstInt(88787); CstInt(-5)])))) emptyEnv;;
staticTC (Min((Of([CstInt(66); CstInt(8); CstInt(88787); CstInt(-5)])))) emptyEnv;; 

staticTC predicate emptyEnv;;
staticTC (Decapitate(ins1)) emptyEnv;;

staticTC (ApplyFirst( (predicate),(ins3) )) emptyEnv;;
staticTC (ApplyFirst( (predicate),(ins2) )) emptyEnv;;
staticTC (ForAll( (predicate),(ins3) )) emptyEnv;;
staticTC (Exist( (predicate),(ins3) )) emptyEnv;;
  
staticTC (Map( (times2),(ins1) )) emptyEnv;; 
staticTC (Filter( (predicate),(ins3) )) emptyEnv;;

staticTC fact emptyEnv;; 
staticTC eIntC emptyEnv;; 




