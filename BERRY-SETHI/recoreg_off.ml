open Char;;

type automate_det =
  {
    transitions : (char,int) Hashtbl.t array;
    init : int;
    final : int list;
  };;


type automate_det_nonproj = 
  {
    transitions : (char,char) Hashtbl.t array;
    init : char;
    final : char list;
  };;


(*Automate exemple qui reconnait le mot aa  *)

let h0 = Hashtbl.create 1;;
let h1 = Hashtbl.create 1;;
let h2 = Hashtbl.create 1;;
Hashtbl.add h1 'a' 2;;
Hashtbl.add h0 'a' 1;;

  
let (auto_aa : automate_det) =
  {
    transitions = [|h0;h1;h2|];
    init = 0;
    final = [2];
  }
;;


(*Automate exemple qui reconnait aa*  *)

let o0 = Hashtbl.create 1;;
let o1 = Hashtbl.create 1;;
Hashtbl.add o1 'a' 1;;
Hashtbl.add o0 'a' 1;;

let (auto_aastar : automate_det) =
  {
    transitions = [|o0;o1|];
    init = 0;
    final = [1];
  }
;;




(* Etape 1 : Reconnaitre un motif dans un texte à l’aide d’un automate*)

let rec appartient l x = match l with
  |[] -> false
  |t::q -> if t=x then true else appartient q x
;;


let rec auto_reco (auto : automate_det) (texte : string) =
  let n = String.length texte in
  let etat_atteint = ref [] in
  let rec evalaut j y = (*evalue l'automate depuis l'état y avec la jieme lettre du texte*)
    let rep = Hashtbl.find auto.transitions.(y) texte.[j] in
    if appartient auto.final rep then
      begin
        etat_atteint := !etat_atteint@[(j,y+1)];
        if j<=n then (evalaut (j+1) rep) else ();
      end
    else
      (if j<=n then (evalaut (j+1) rep) else ());
  in    
  for i = 0 to n-1 do
    try evalaut i auto.init
    with
    |Not_found -> ()
    |Invalid_argument _ -> ()
  done;
  !etat_atteint
;;




(* Etape 2 : construction automate à l'aide de l'algorithme de Berry Sethi *)

type exp_reg =
  |Vide
  |Eps
  |Lettre of char
  |Union of (exp_reg * exp_reg)
  |Concat of (exp_reg * exp_reg)
  |Etoile of exp_reg
;;


(*exemple 1 : ((ab)*|aba*)  

let e1 = Union(   Etoile( Concat( Lettre('a') , Lettre('b') )),   Concat( Concat(Lettre('a'),Lettre('b')), Etoile(Lettre('a')) )   );;


(*exmple simple : ab* *)

let (e_simple : exp_reg) = Concat(Lettre 'a', Etoile(Lettre 'b'));;


(* LINEARISATION *)


let rec length_l l = match l with
  |[] -> 0
  |t::q -> 1+length_l q
;;


let rec nb_lettres_exp_reg = function
  |Lettre x -> 1
  |Etoile e -> nb_lettres_exp_reg e
  |Concat (e1,e2) -> (nb_lettres_exp_reg e1)+(nb_lettres_exp_reg e2)
  |Union (e1,e2) -> (nb_lettres_exp_reg e1)+(nb_lettres_exp_reg e2)
  |Eps -> 0
  |Vide -> 0
;;



let rec lettres_dans_exp_reg = function
  |Lettre x -> [x]
  |Etoile e -> lettres_dans_exp_reg e
  |Concat (e1,e2) -> (lettres_dans_exp_reg e1)@(lettres_dans_exp_reg e2)
  |Union (e1,e2) -> (lettres_dans_exp_reg e1)@(lettres_dans_exp_reg e2)
  |Eps -> []
  |Vide -> []
;;


let list_to_tab l  =
  let n = length_l l in
  let tab = Array.make n 'z' in
  let rec aux = function
    |[]-> ()
    |t::q -> tab.(n-(length_l q)-1)<-t;
             aux q;
  in
  aux l;
  tab;;



let rec line (i : int) = function
  |Eps -> Eps
  |Vide -> Vide
  |Lettre x ->  Lettre (char_of_int (i+65))
  |Etoile e -> Etoile (line i  e)
  |Concat (e1,e2) -> Concat((line i e1), (line (i+(length_l (lettres_dans_exp_reg e1))) e2))
  |Union (e1,e2) -> Union( (line i e1), (line (i+(length_l (lettres_dans_exp_reg e1))) e2))
;;


let rec deline exp_line tab =
  let cpt = ref 0 in
  let rec aux e j = match e with
    |Lettre x -> Lettre tab.(j)
    |Etoile e -> Etoile(aux e j)
    |Concat (e1,e2) -> Concat((aux e1 j),(aux e2 (j+(nb_lettres_exp_reg e1))))
    |Union (e1,e2) -> Union( (aux e1 j) , (aux e2 (j+(nb_lettres_exp_reg e1))))
    |Eps -> Eps
    |Vide -> Vide
  in aux exp_line !cpt  
;;



(* FIN LINEARISATION *)


(*FONCTIONS AUXILIARES *)



let rec contient_eps (er : exp_reg) : bool = match er with
  |Vide -> false
  |Eps -> true
  |Lettre(c) -> false
  |Etoile(_) -> true
  |Union(e1,e2) -> (contient_eps e1) || (contient_eps e2)
  |Concat(e1,e2) -> (contient_eps e1) && (contient_eps e2)
;;



let rec first = function
  |Eps -> []
  |Vide -> []
  |Lettre x -> [x]
  |Etoile e -> first e
  |Union (e1,e2) -> (first e1)@(first e2)
  |Concat (e1,e2) -> if (not (contient_eps e1)) then first e1 else
                       (first e1)@(first e2)
;;



let rec last = function
  |Eps -> []
  |Vide -> []
  |Lettre x -> [x]
  |Etoile e -> last e
  |Union (e1,e2) -> (last e1)@(last e2)
  |Concat (e1,e2) -> if (contient_eps e2) then (last e1)@(last e2) else (last e2)
;;

let digra_jonction e1 e2 =
  let rec aux (c : char) (l : char list) = match l with
    |[] -> []
    |t::q -> [c;t]::(aux c q)
  in
  let rec aux1 = function
    |[] -> []
    |t::q -> (aux t (first e2))@(aux1 q)
  in aux1 (last e1)
;;


let rec digra = function
  |Eps -> []
  |Vide -> []
  |Lettre x -> []
  |Etoile(e1) -> (digra e1)@(digra_jonction e1 e1)
  |Union (e1,e2) -> (digra e1)@(digra e2)
  |Concat (e1,e2) -> (digra e1)@(digra e2)@(digra_jonction e1 e2)
;;


(* fonction qui élimine doublon *)

let rec ed l = match l with
  |[] -> []
  |t::q -> if (appartient q t) then (ed q) else t::(ed q);;



let digra_off e = ed (digra e);;



(* FIN FONCTIONS AUXILIAIRES *)



let berry_sethi (e : exp_reg) : automate_det_nonproj =
  let elin = line 0 e in
  let n = nb_lettres_exp_reg e in
  let l_final e1 e2 = if contient_eps e1 then ['0']@(last e2) else (last e2) in
  let (auto : automate_det_nonproj) =
    {
      init = '0';
      final = l_final e elin;
      transitions = Array.make (n+1) (Hashtbl.create 1);
    }
  in
  for i=0 to n do
    auto.transitions.(i)<-(Hashtbl.create (n+1));
  done;
  let rec first_aux l = match l with
    |[] -> ()
    |t::q -> Hashtbl.add auto.transitions.(0) t t;
             first_aux q;
  in
  let rec digra_aux l = match l with
    |[] -> ()
    |t::q -> let t1 = list_to_tab t in Hashtbl.add auto.transitions.(code (t1.(0))-65+1) t1.(1) t1.(1); digra_aux q;
  in
  first_aux (first elin);
  digra_aux (digra_off elin);
  auto;;




let projection (auto_bs : automate_det_nonproj) (exp : exp_reg) : automate_det =
  let n = nb_lettres_exp_reg exp in
  let tab_assos = list_to_tab (lettres_dans_exp_reg exp) in
  let l_final = ref [] in
  let rec aux_l_final = function
    |[] -> ()
    |t::q -> if t != '0' then l_final := !l_final@[(code t)-65+1] else l_final := !l_final@[0];
             aux_l_final q
  in
  let tr = Array.make (n+1) (Hashtbl.create 1) in
  for i = 0 to n do
    tr.(i) <- Hashtbl.create (n+1);
  done;
  let add_une_tr z w =
    let r = Hashtbl.find auto_bs.transitions.(w) (chr (z+65)) in
    Hashtbl.add tr.(w) tab_assos.((code r)-65) (z+1);
  in
  let add_tr =
    for x=0 to n-1 do
      for y=0 to n do
        try add_une_tr x y
        with
        |Not_found -> ()
      done;
    done;
  in
  add_tr;
  aux_l_final auto_bs.final;
  let (auto_final : automate_det) = {
      init = 0;
      final = !l_final;
      transitions = tr;
    }
  in
  auto_final
;;  
