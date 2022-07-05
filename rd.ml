#use "functions.ml";;

(* Funzione che prende una lista di identificatori e a tutti assegna il 
   questmark, come valore nella coppia (ide, Questmark) *)
let questMark (l:ide list) = List.map (fun a -> (a, Qestmark)) l;;


(* Funzione che prende una lista di blocchi e una label e restituisce il 
   blocco del programma con tale label *)
let rec block_l (b:blocks list) l = match b with
    [] -> failwith "nessun blocco ha questo label"
  | hd::tl -> if ( ( match hd with
             Bc primcom -> (match primcom with
                              Bassign (i,a,lab) -> lab
                            | Bskip (lab) -> lab
                           )
           | Bb primbool -> (match primbool with
                               Bbexp (b,lab) -> lab )
                   ) = l) then hd else block_l tl l;;

(* Funzione che prende una lista di coppie dilabel e una label e restituisce
   una nuova lista che contiene gli elementi di list che hanno come secondo 
   elemento la label l passata *)
let rec flow_match (list:(lab * lab) list) (l:lab) = match list with
    [] -> []
  | hd::tl -> if(match hd with
                   (a,b) -> b = l)then hd::flow_match tl l
              else flow_match tl l;;

(* Funzione che prende una lista ed un elemento e restituisce la lista senza
   l'elemento passatogli *)
let rec remove y = function
    [] -> []
  | x::xs -> if x = y then xs else x::remove y xs;;

(* Funzione che prende due liste e restituisce una nuova lista uguale alla 
   prima ma priva degli elementi della seconda *)
let rec setdiff xs = function
    [] -> xs
  | y::ys -> setdiff (remove y xs) ys;;

(* Funzione che prende una lista di blocchi bl  e un identificatore ide
 e restituise tutte le coppie (ide * lab) presenti nel programma *)
let rec sel_lab (bl) ide =  match bl with
    [] -> []
  | hd::tl -> (match hd with
                 Bc primcom -> (match primcom with
                                  Bassign (i,a,l) -> if i = ide
                                            then [(i,l)] @ sel_lab tl ide
                                                     else sel_lab tl ide
                                | Bskip l -> sel_lab tl ide
                               )
               | Bb primbool -> sel_lab tl ide
              );;


(* Funzione prende un programma non annotato e una label e restituisce una 
 lista (ide*lab) che rappresentano le coppie da eliminare per la RD analisi*)
let killRD (c:com) (l:lab) = match block_l (blocks (annotate c) ) (l) with
      Bc primcom -> (match primcom with
                       Bassign (i,a,l) -> union
                                            [(i, Qestmark)]
                                            (sel_lab (blocks (annotate c)) i)
                     | Bskip (l) -> [])
   | Bb primbool -> (match primbool with
                       Bbexp (b,l) -> []);;


(* Funzione gen che preso un blocco restituisce una lista (identificatori *
   label) che rappresentano le coppie da generare nella RD analisi *)
let genRD (b:blocks) = match b with
    Bc primcom -> (match primcom with
                     Bassign (i,a,l) -> [(i,l)]
                   | Bskip (l) -> [] )
  | Bb primbool -> [];;

(* rden: prende un programma non annotato, una label e un intero e 
         restituisce una lista (ide * lab) che rappresenta la RD analisi in
         entrata al blocco l dopo n passi di iterazione 

   rdex: prende un programma non annotato, una label e un intero e
         restituisce una lista (ide * lab) che rappresenta la RD analisi in
         uscita al blocco l dopo n passi di iterazioni 

 passo2: prende una lista (lab * lab) e restituisce l'unione delle rdEX 
         passodogli come parametro il primo elemento della lista *)
let rec rden (c:com) (l:lab) n =
  if (n = 0) then
    []
  else
    if (n = 1) then
      questMark (fv c)
    else
      let rec passo2 (lista: (lab * lab) list) = match lista with
          [] -> []
        | hd::tl -> union ((rdex c (fst hd) (n-1))) (passo2 tl) in
      passo2(flow_match(flow(annotate c)) l)
and
  rdex (c:com) (l:lab) n =
  if (n = 0) then
    []
  else
    union (setdiff(rden c l (n-1)) (killRD c l))
      (genRD (block_l(blocks(annotate c)) l));;

(* Funzione che preso un programma non annotate e un intero restituisce una
   lista di liste (ide*lab) che contiene tutte le entry della RD analisi *)
let rec rdentry c n =
  if(n = 0) then
    []
  else
    rdentry c (n-1) @ [rden c (L n) (n*2 - 1)];;

(* Funzione che preso un programma non annotato e un intero restituisce 
una lista di liste (ide*lab) che contiene tutte le exit della RD analisi *)
let rec rdexit c n =
  if(n = 0) then
    []
  else
    rdexit c (n-1) @ [rdex c (L n) (n*2)];;

(* Funzione che prende un programma non annotato e resituisce una tripla
   contenente tutta la RD entry in prima posizione, la RD exit in seconda
   posizione e il comando annotato in terza posizione *)
let rec rdanalisi c =
  (rdentry c (List.length (label(annotate c))),
   rdexit c (List.length (label(annotate c))), annotate c);;
