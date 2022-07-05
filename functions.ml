(* I tipi Aexp, Bexp e Com *)

(* Var *)

type ide = string    

(* Aexp *)
type aexp =     
      | Eint of int     
      | Den of ide
      | Prod of aexp * aexp
      | Sum of aexp * aexp
      | Diff of aexp * aexp

(* Bexp *)
and bexp = 
      | True
      | False
      | Eq of aexp * aexp
      | Less of aexp * aexp
      | Greater of aexp * aexp
      | Or of bexp * bexp
      | And of bexp * bexp
      | Not of bexp
          
(* Com *)
type com = 
     | Skip
     | Assign of ide * aexp
     | Ifthenelse of bexp * com * com
     | While of bexp * com
     | Cseq of com * com

(* Tipi che sono del progetto *)

(* Lab: questo è il tipo delle etichette.
 Questmark sta per il punto di domanda.
   Si assume che vengano assegnati interi d'ordine crescente.
   Altre implementazioni non sono ammesse  *)
type lab =
      Qestmark
    | L of int


(* I blocchi sono: 
   o assegnamenti e skip etichettati
   o espressioni booleane etichettate, 
   che derivano da if e while *)

(* Blocchi da comandi *)
type primcom =
     | Bassign of ide * aexp * lab
     | Bskip of lab

(* Blocchi da espressioni booleane *)
type primbool =
     | Bbexp of bexp * lab

(* Blocchi *)
type blocks =
     | Bc of primcom
     | Bb of primbool

           
(* Comstar, è il tipo dei comandi annotati *)
type stms =
| B of primcom
| Bifthenelse of primbool * stms * stms
| Bwhile of primbool * stms
| Bcseq of stms * stms
         
(* tipi degli insiemi *)
type setofblocks = blocks list
type fvset = ide list
type labset = lab list
type edgeset = (lab*lab) list

(* l'analisi RD deve restituire un elemento del tipo rd *)
type rdset = (ide * lab) list
type rdentry = rdset list
type rdexit = rdset list
type rd = rdentry * rdexit

(* l'analisi AE deve restituire un elemento del tipo ae *)
type aeset = aexp list
type aeentry = aeset list
type aeexit = aeset list
type ae = aeentry * aeexit

(* Funzione che controlla se l'elemento e è presente nella lista l *)
let contain e l = List.exists (fun a -> a = e) l;;

(*prende una lista ed elimina gli elementi doppi*)
let elimina l = List.fold_right (fun a b -> if (contain a b) then b else [a]@b) l [];;

(* Funzione che compie l'unione insiemistica tra due liste*)
let union l1 l2 = elimina (l1 @ l2);;


(* Funzione che prende un espressione aritmetica e restituisce le variabili
    presenti *)
let rec ae (a:aexp) = match a with
    Eint l -> []
  | Den i -> [i]
  | Prod (a1,a2) -> ae a1 @ ae a2
  | Sum (a1,a2) -> ae a1 @ ae a2
  | Diff (a1,a2) -> ae a1 @ ae a2;;

(* Funzione che prende un espressione boolena e restituisce le variabili
    presenti *)
let rec be (p:bexp) = match p with
    Eq (a1,a2) -> union (ae a1) (ae a2)
  | Less (a1,a2) -> union (ae a1) (ae a2)
  | Greater (a1,a2) -> union (ae a1) (ae a2)
  | _ -> [];;

(* Funzione che prende un comando non annotato e restituisce tutte le 
   variabili presenti all'interno *)
let rec fv (c:com) = match c with
    Skip -> []
  | Assign (i,a) -> union [i] (ae a)
  | Ifthenelse (b, c1, c2) -> union (be b) (union (fv c1) (fv c2))
  | While (b,c1) -> union (be b) (fv c1)
  | Cseq (c1,c2) -> union (fv c1) (fv c2);;

(* Funzione ann che prende un programma e un intero e restituisce un 
   programma annotato *)
let rec ann (c:com) n =  match c with
       Skip -> B (Bskip (L (n)))
  | Assign (i,a) -> B (Bassign (i,a,L (n)))
                  
  | Ifthenelse (b,c1,Cseq(c2,c3)) -> Bifthenelse (Bbexp(b,L (n)),                       ann c1 (n+1), ann (Cseq(c2,c3)) (n+3))
                                   
  | Ifthenelse (b,Cseq(c1,c2),c3) -> Bifthenelse (Bbexp(b,L (n)),                         ann (Cseq(c1,c2)) (n+1), ann c3 (n+3))
                                   
  | Ifthenelse(b,c1,c2)->Bifthenelse (Bbexp(b,L (n)),ann c1 (n+1),
               ann c2 (n+2))
                       
  | While (b,c) -> Bwhile(Bbexp (b,L (n)),ann c (n+1))
  | Cseq (While (b,c),c2) -> Bcseq ( ann (While (b,c) ) n , ann c2 (n+3) )
  | Cseq ((Ifthenelse (b,c1,c2)), c3) -> Bcseq (ann (Ifthenelse (b,c1,c2)) n,
                                                 ann c3 (n+3) )
  | Cseq (c1,c2) -> Bcseq (ann c1 (n), ann c2 (n+1));; 

(* Funzione annotate che prende un programma e su di esso chiama la funzione 
   ann, passando come valore intero 1 *)
let annotate (c:com) = ann c 1;;


(* Funzione init che prende un stms e restituisce il punto di ingresso del
   costrutto *)
let rec init (cAnn:stms) =  match cAnn with
     B primcom -> (match primcom with
                     Bassign (i,a,l) -> l
                   | Bskip (l) -> l )
                
   | Bifthenelse (primbool,c1,c2) ->(match primbool with
                                       Bbexp (b,l) -> l )
                                  
   | Bwhile (primbool,c1)  -> (match primbool with
                                 Bbexp (b,l) -> l )

   | Bcseq (c1,c2)  -> init c1;;


(* Funzione final che prende un stms e restituisce i punti di usicta del
   costrutto *)
let rec final (cAnn:stms) = match cAnn with
    B primcom -> (match primcom with
                   Bassign (i,a,l) -> [l]
                  | Bskip (l) -> [l] )
               
  | Bifthenelse (primbool, c1,c2) ->  (union (final c1)  (final c2))
  | Bwhile (primbool,c1) -> (match primbool with
                               Bbexp (b,l) -> [l] )
  | Bcseq (c1,c2) -> (final c2);; 



(* Funzione blocks che prende un stmt e restituisce una lista contentente 
   gli elementi primitivi  di un programma *)
let rec blocks (cAnn:stms) = match cAnn with
    B primcom -> [Bc primcom]
  | Bcseq (c1,c2) -> union (blocks c1) (blocks c2)
  | Bifthenelse (b,c1,c2) -> union ([Bb b]) (union (blocks c1) (blocks c2))
  | Bwhile (b,c1) ->union ([Bb b]) (blocks c1);;


(* Funzione che prende un comando annotato e restituisce una lista con 
   tutte le label *)
let rec label (cAnn:stms) = match cAnn with
    B primcom -> (match primcom with
                   Bassign (i,a,l) -> [l]
                  | Bskip (l) ->[l] )
  | Bifthenelse ((Bbexp (b,l)), c1,c2) -> union ([l])
                                            (union (label c1) (label c2))
  | Bwhile ((Bbexp (b,l)),c1) -> union ([l]) (label c1) 
  | Bcseq (c1,c2) -> union (label c1) (label c2);;



(* Funzione dupla che prende una lista e un elemento e restituisce delle
   duple scritte come (testa della lista,elemento) *)
let rec dupla l e = match l with
    [] -> []
  | hd::tl -> (hd,e)::dupla tl e;;


(* Funzione flow che preso un comando annotato restituisce una lista di duple
   (Label * Label )*)
let rec flow (cAnn:stms) = match cAnn with
    B p -> []
  | Bifthenelse ((Bbexp (b,l)),s1,s2) -> union (flow s1)
                                           (union (flow s2)
                                              ([(l,init s1);(l,init s2)]) )
  | Bwhile ((Bbexp (b,l)), s)-> union (flow s)
                                  (union ([(l,init s)])
                                     (dupla (final s) l ))
  | Bcseq (s1,s2) -> union (flow s1)
                       (union (flow s2) (dupla (final s1) (init s2) ) );;


(* Funzione search che prende un elemento e una lista e restituisce true se
   quell'elemento è presente nella lista, false altrimenti *)
let rec search el l = match l with
    [] -> false
  | hd::tl -> if(hd = el) then true else search el tl;;


(* Funzione double che prende una lista e controlla se sono presenti dei 
   doppioni *)
let rec double  l = match l with
    [] -> false
  | hd::tl -> if search hd l then true else double tl;;

(* Funzione check che prende un comando annotato e controlla che tutte le 
   etichette assegantoli siano uniche *)
let check (cAnn:stms) = double (label (cAnn));;
