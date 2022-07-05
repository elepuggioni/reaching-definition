#use "rd.ml";;

(*Funzione che inverte una lista *)
let list_reverse l = List.fold_left (fun a b -> b::a) [] l;;

(* Funzione che restituisce l'intersezione tra due liste*)
let intersection l1 l2 = list_reverse ( List.fold_left (fun acc x -> if(List.exists (fun y -> y = x) l1) then x::acc else acc) [] l2);;


(* Funzione che prende un comando e restituisce le espressioni coinvolte*)
let rec expressions (c:com) = match c with
    Skip -> []
  | Assign (i,a) -> [a]
  | Ifthenelse (b, c1, c2) -> union (expressions c1) (expressions c2)
  | While (b,c1) -> (expressions c1)
  | Cseq (c1,c2) -> union (expressions c1) (expressions c2);;


(* Funzione che prende una espressione aritmetica e restituisce le espressioni 
   aritmetiche che compongono il comando *)
let rec aexpA a = match a with
    Eint i -> []
  | Den i -> []
  | Prod (f1,f2) -> union (aexpA f1) (union [Prod (f1,f2)] (aexpA f2))
  | Sum (a1,a2) -> union (aexpA a1) (union [Sum (a1,a2)] (aexpA a2))
  | Diff (d1,d2) -> union (aexpA d1) (union ([Diff (d1,d2)]) (aexpA d2)) ;;


(* Funzione che prende una espressione booleana e restituisce le espressioni 
   aritmetiche presenti *)
let rec aexpB b = match b with
    Eq (ae1,ae2) -> union (aexpA ae1) (aexpA ae2)
  | Less (ae1,ae2) -> union (aexpA ae1) (aexpA ae2)
  | Greater (ae1,ae2) -> union (aexpA ae1) (aexpA ae2)
  | Or (b1,b2) -> union (aexpB b1) (aexpB b2)
  | And (b1,b2) -> union (aexpB b1) (aexpB b2)
  | Not (b1) -> aexpB b1
  | _ -> [] ;;

(* Funzione che prende una lista di espressioni aritmetiche e restituisce gli
   identificatori presenti  *)
let rec fvAexp a = match a with
    [] -> []
  | hd::tl -> union (ae hd) (fvAexp tl);;


(* Funzione che prende un blocco ed un comando e restituisce una lista di 
   espressioni aritmetiche  da eliminare per la AE analisi *)
let killAE b c  = match b with
    Bc primcom -> (match primcom with
                     Bassign (x,a,l) ->  let aPrimo = expressions c in
                                         if search x (fvAexp aPrimo)
                                         then aPrimo
                                         else []
                   | Bskip (l) -> [] )
                
  | Bb primbool -> [];;


(* Funzione che prende un blocco ed  e restituisce una lista di espressioni 
   aritmetiche da generare nella RD analisi *)
let genAE b = match b with
    Bc primcom -> (match primcom with
                     Bassign (x,a,l) -> let aPrimo = aexpA a
                                        in if (search x (fvAexp aPrimo))
                                           then []
                                           else aPrimo      
                   | Bskip (l) -> [] )
                
  | Bb primbool -> (match primbool with
                      Bbexp (b,l) -> aexpB b ) ;;


(* aeEN: prende un programma non annotato, una label e un intero e 
         restituisce una lista che rappresenta la AE analisi in
         entrata al blocco l dopo n passi di iterazione 

   aeEX: prende un programma non annotato, una label e un intero e
         restituisce una lista che rappresenta la AE analisi in
         uscita al blocco l dopo n passi di iterazioni 

 passo2: prende una lista (lab * lab) e restituisce l'intersezione delle aeEX 
         passodogli come parametro il primo elemento della lista *)
let rec aeEN (c:com) (l:lab) n =
  if (n = 0) then
    expressions c
  else
    if( l = init(annotate c) ) then
     []
    else
      let rec passo2 (lista) = match lista with
          [] -> []
        | hd::[] -> ((aeEX c (fst hd) (n-1) ))
        | hd::tl -> intersection ((aeEX c (fst hd) (n-1) )) (passo2 tl) in
      passo2 (flow_match (flow (annotate c)) l)
  and
    aeEX (c:com) (l:lab) n =
    if (n = 0) then
      expressions c
    else
      union (setdiff (aeEN c l (n-1))
             ( killAE (block_l (blocks (annotate c)) l) c ) )
        (genAE (block_l (blocks (annotate c)) l) );;


(* Funzione che preso un programma non annotato e un intero restituisce una
   lista di liste che contiene tutte le entry della AE analisi *)
let rec aeEntry c n =
  if (n = 0) then
    []
  else
    aeEntry c (n-1) @ [aeEN c (L n) (n*2 -1) ];;

(* Funzione che preso un programma non annotato e un intero restituisce 
una lista di liste che contiene tutte le exit della AE analisi *)
let rec aeExit c n =
  if (n = 0) then
    []
  else
    aeExit c (n-1) @ [ aeEX c (L n) (n*2) ];;

(* Funzione che prende un programma non annotato e resituisce una tripla
   contenente tutta la AE entry in prima posizione, la AE exit in seconda
   posizione e il comando annotato in terza posizione *)
let rec aeanalisi c =
  (aeEntry c (List.length (label(annotate c))),
                aeExit c (List.length (label(annotate c))), annotate c);;
