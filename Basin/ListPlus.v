(* ----------------------------------------------------------------- *)
(*                    Additional List handlings                      *)
(* ----------------------------------------------------------------- *)

From Practice Require Import Basin.Base.
From Coq Require Export Sorting.


Set Implicit Arguments.
Generalizable All Variables.

(* TODO Drop this *)

(*
(* ----------------------------------------------------------------- *)
(*               Lemmas and boolean version of Forall2               *)
(* ----------------------------------------------------------------- *)

Section forallb2.
Variable A B: Type.
Variable R: A -> B -> bool.

Fixpoint forall2b (l: list A) (m: list B) :=
  match l, m with
  | [], [] => true
  | x :: l', y :: m' => R x y && forall2b l' m'
  | _, _ => false
  end.

Property Forall2P: forall l m, reflect (Forall2 R l m) (forall2b l m).
Proof.
  move=> l m. apply: Bool.iff_reflect. split.
  - elim=> //= x y l' m' Rxy Hlm IH. by apply/andP.
  - elim: l m=> [| x l' IH] [| y m'] //=.
    move/andP => [? /IH ?]. by constructor.
Qed.

End forallb2.


Section Forall2.
Variable A B: Type.
Variable R: A -> B -> Prop.

Property Forall2_inv: forall x y l m,
  Forall2 R (x :: l) (y :: m) -> R x y.
Proof. move=> x y l m H. inversion H; subst=> //. Qed.

Property Forall2_inv_tail: forall x y l m,
  Forall2 R (x :: l) (y :: m) -> Forall2 R l m.
Proof. move=> x y l m H. inversion H; subst=> //. Qed.


Lemma Forall2_single: forall x y,
  Forall2 R [x] [y] <-> R x y.
Proof. move=> x y. split=> H. apply: Forall2_inv; eauto. by constructor. Qed.

Lemma Forall2_len: forall l m,
  Forall2 R l m -> length l = length m.
Proof. move=> l m. elim=> //= x y l' m' _ _. lia. Qed.



Lemma Forall2_nth l m:
  Forall2 R l m <->
  length l = length m /\ forall i d d', i < length l -> R (nth i l d) (nth i m d').
Proof.
  split.
  - (* -> *)
    elim=> [| a b {}l {}m Rab H [IH1 IH2]]. { split=> //=. lia. }
    split. rewrite /= IH1 //.
    move=> [| i] d d'=> //= ?. apply /IH2. lia.
  - (* <- *)
    move: m. elim: l=> [| a l IH] [| b m] //= [H1 H2]; try discriminate.
    constructor.
    + apply: (H2 0)=> //. lia.
    + apply: IH. split. by injection H1.
      move=> i d d' H. apply: (H2 (S i) d d'). lia.
Qed.

Lemma Forall2_rev: forall l m,
  Forall2 R l m -> Forall2 R (rev l) (rev m).
Proof.
  move=> l m. elim=> //= x y {}l {}m Hh Ht IH.
  apply /Forall2_app=> //. by constructor.
Qed.

End Forall2.


Add Parametric Morphism U V: (@Forall2 U V)
  with signature equiv ==> eq ==> eq ==> iff as Forall2_mor.
Proof.
  move=> P Q E l m. do 4 red in E. split.
  all: elim=> // a b {}l {}m.
  all: rewrite E || rewrite -E. all: by constructor.
Qed.


Instance Forall2_refl A R `(Reflexive A R): Reflexive (Forall2 R).
Proof. red. elim=> // a l' IH. by constructor. Qed.

Instance Forall2_sym A R `(Symmetric A R): Symmetric (Forall2 R).
Proof.
  red=> x y. elim=> // a b {}x {}y HR Hxy IH.
  constructor=> //. by apply/H.
Qed.

Instance Forall2_trans A R `(Transitive A R): Transitive (Forall2 R).
Proof.
  red=> x y + Hxy. elim: Hxy => // a b {}x {}y HR Hxy + z Hb.
  case E: (b :: y) _ /Hb=> // [b' c y' {}z + +].
  move: E=> [<- <-] Hh Ht IH. constructor.
  by transitivity b. by apply /IH.
Qed.


(* ----------------------------------------------------------------- *)
(*               Lemmas and boolean version of Sorted                *)
(* ----------------------------------------------------------------- *)

Section Sortedb.
Variable T: Type.
Variable r: T -> T -> bool.

Fixpoint Sortedb (l: list T): bool :=
  match l with
  | [] => true
  | x :: l' => if l' isn't x' :: _ then true
    else r x x' && Sortedb l'
  end.

Property Sortedb_red: forall a b l,
  Sortedb (a :: b :: l) = r a b && Sortedb (b :: l).
Proof. reflexivity. Qed.

Property SortedP: forall l, reflect (Sorted r l) (Sortedb l).
Proof.
  move=> l. apply: Bool.iff_reflect. split.
  - elim=> // a {}l + + Hh. elim: Hh=> // b {}l Hh Ht IH.
    rewrite Sortedb_red. by apply/andP.
  - elim: l=> // a. case=> [| b l]. by constructor.
    rewrite Sortedb_red=> IH /andP[Hh Ht].
    constructor. by apply: IH. by constructor.
Qed.

End Sortedb.

Lemma HdRel_iff: forall T (R: T -> T -> Prop) a b l,
  HdRel R a (b :: l) <-> R a b.
Proof. move=> T R a b l. split. apply: HdRel_inv. apply: HdRel_cons. Qed.


Add Parametric Morphism U: (@HdRel U)
  with signature equiv ==> eq ==> eq ==> iff as HdRel_mor.
Proof.
  move=> P Q E a. do 6 red in E. case=> // b l.
  rewrite !HdRel_iff //.
Qed.

Add Parametric Morphism U: (@Sorted U)
  with signature equiv ==> eq ==> iff as Sorted_mor.
Proof.
  move=> P Q E. elim=> // a l' IH. split=> H.
  all: move: (Sorted_inv H)=> [].
  all: rewrite IH E || rewrite -IH -E. all: apply: Sorted_cons.
Qed.


Section Sorted.
Variable T: Type.
Variable R: T -> T -> Prop.


Lemma Sorted_app: forall l m d1 d2,
  Sorted R l -> Sorted R m -> R (last l d1) (hd d2 m) -> Sorted R (l ++ m).
Proof.
  move=> l m ? ? Hl Hm.
  elim: Hl=> //= a {}l Ht IH Hh Hr.
  case: Hh Ht IH Hr=> [_ |b {}l Hh Ht] IH Hr.
  - constructor=> //= {Hm IH}. by case: m Hr; constructor.
  - constructor. by apply: IH. by constructor.
Qed.

Lemma Sorted_filter: Transitive R ->
  forall (p: T -> bool) l, Sorted R l -> Sorted R (filter p l).
Proof.
  move=> Tr p l.
  move/(Sorted_StronglySorted Tr)=> H. apply: StronglySorted_Sorted.
  elim: H=> /=. constructor.
  move=> a {}l Ht IH Hh.
  case: (p a)=> //. constructor=> //.
  apply: incl_Forall. apply: incl_filter. done.
Qed.

Lemma Sorted_nth: Transitive R ->
  forall d1 d2 l, Sorted R l <-> forall m n, m < n < length l -> R (nth m l d1) (nth n l d2).
Proof.
  move=> Tr ? ? l. split.
  - (* -> *)
    move/(Sorted_StronglySorted Tr).
    elim=> [|a {}l Ht IH Hh] m n []. simpl; lia.
    move: m n=> [| m'] [| n'] /= Lt1 Lt2. all: try lia.
    + move: Hh=> /Forall_nth. apply. lia.
    + apply: IH. lia.
  - (* <- *)
    elim: l=> // a l IH H. constructor.
    + apply: IH=> m n [Hm Hn].
      move: (H (S m) (S n))=> /=. apply. lia.
    + move: (H 0 1)=> /= {H IH}. case: l=> //= b l H.
      constructor. apply: H. lia.
Qed.

(* To host the abbreviation representation *)
Lemma Sorted_inv_Forall: Transitive R ->
  forall a l, Sorted R (a :: l) <-> Forall (R a) l /\ Sorted R l.
Proof.
  move=> Tr a l. split.
  - move=> H. split. by apply: Sorted_extends. move: (Sorted_inv H)=> [] //.
  - move=> [Hh Ht]. apply: StronglySorted_Sorted.
    constructor=> //. by apply: Sorted_StronglySorted.
Qed.

End Sorted.


Lemma Sorted_rev: forall T (R: T -> T -> Prop) l,
  Sorted R l -> Sorted (flip R) (rev l).
Proof.
  move=> T R. elim=> //= a l IH.
  move/(@Sorted_inv _ _ a)=> [Ht Hh].
  case: Hh Ht IH=> [|b {}l Hh] Ht IH /=. { by constructor. }
  have {}Hh: R (hd a [a]) (last (rev l ++ [b]) a) by rewrite last_last.
  apply: Sorted_app _ _ Hh. by apply: IH. by constructor.
Qed.

Lemma Sorted_map: forall S T (RS: S -> S -> Prop) (RT: T -> T -> Prop) (f: S -> T) l,
  (forall s s', RS s s' -> RT (f s) (f s')) -> Sorted RS l -> Sorted RT (map f l).
Proof.
  move=> S T RS RT f l Im.
  elim=> //= a {}l Ht IH Hh. constructor=> // {IH Ht}.
  case: Hh=> //= b {}l H. constructor. by apply: Im.
Qed.

Section Sorted2.
Variable T: Type.
Variable R1 R2: T -> T -> Prop.

Corollary Sorted_impl: (forall t t', R1 t t' -> R2 t t') ->
  forall l, Sorted R1 l -> Sorted R2 l.
Proof. move=> Im l. rewrite -{2}(map_id l). by apply: Sorted_map. Qed.

Lemma Sorted_and: forall l,
  Sorted R1 l -> Sorted R2 l -> Sorted (fun t t' => R1 t t' /\ R2 t t') l.
Proof.
  elim=> // a l IH H1 H2.
  move: (Sorted_inv H1) (Sorted_inv H2)=> [{}H1 Hh1] [{}H2 Hh2].
  constructor. by apply IH. move=> {IH H1 H2}.
  case: l Hh1 Hh2=> // b l.
  rewrite !HdRel_iff //.
Qed.

End Sorted2.


Lemma Sorted_seq: forall m n, Sorted lt (seq m n).
Proof.
  move=> + n.
  elim: n=> //= n IH m. constructor=> // {IH}.
  case: n=> //= n. constructor. lia.
Qed.


(* ----------------------------------------------------------------- *)
(*                         Reverse Indexing                          *)
(* ----------------------------------------------------------------- *)

Section Rth.
Variable A: Type.

Definition rth (n: nat) (l: list A) (def: A) := nth n (rev l) def.

Lemma rth_hd: forall (a: A) l d,
  rth (length l) (a :: l) d = a.
Proof.
  move=> a l d. rewrite /rth /=.
  rewrite app_nth2 rev_length. lia. rewrite Nat.sub_diag //.
Qed.

Lemma rth_hd2: forall (a: A) l n d,
  n = length l -> rth n (a :: l) d = a.
Proof. move=> a l _ d ->. apply: rth_hd. Qed.


Lemma rth_tl: forall (a: A) l n d,
  n < length l -> rth n (a :: l) d = rth n l d.
Proof. move=> a l n d. rewrite /rth /= -rev_length. apply: app_nth1. Qed.

Lemma rth_hd_or_tl: forall (a: A) l n d,
  n <= length l -> rth n (a :: l) d = a \/ rth n (a :: l) d = rth n l d.
Proof.
  move=> a l n d.
  case/Lt.le_lt_or_eq=> [Hm | ->];
  by [ right; apply: rth_tl | left; apply: rth_hd ].
Qed.


Lemma app_rth1: forall l l' n d,
  n < length l -> rth n (l' ++ l) d = rth n l d.
Proof. move=> l l' n d. rewrite /rth rev_app_distr -rev_length. apply: app_nth1. Qed.

Lemma app_rth2: forall l l' n d,
  n >= length l -> rth n (l' ++ l) d = rth (n - length l) l' d.
Proof. move=> l l' n d. rewrite /rth rev_app_distr -rev_length. apply: app_nth2. Qed.


Lemma rth_In: forall l n d, n < length l -> In (rth n l d) l.
Proof. move=> l n d. rewrite /rth in_rev -rev_length. apply: nth_In. Qed.

Lemma In_rth l x d : In x l ->
  exists n, n < length l /\ rth n l d = x.
Proof. rewrite /rth in_rev. move/(In_nth _ _ d). rewrite rev_length //. Qed.

Lemma rth_overflow: forall l n d, n >= length l -> rth n l d = d.
Proof. move=> l n d. rewrite /rth -rev_length. apply: nth_overflow. Qed.

Lemma rth_indep: forall l n d d',
  n < length l -> rth n l d = rth n l d'.
Proof. move=> l n d d'. rewrite /rth -rev_length. apply: nth_indep. Qed.


Lemma rth_in_or_def: forall l n d,
  {In (rth n l d) l} + {rth n l d = d}.
Proof.
  move=> l n d. rewrite /rth.
  case: (nth_in_or_default n (rev l) d)=> [|->];
  by [left; apply/in_rev | right].
Qed.

End Rth.


Lemma map_rth: forall A B (f: A -> B) l d n,
  rth n (map f l) (f d) = f (rth n l d).
Proof. move=> A B f l d n. rewrite /rth -map_rev map_nth //. Qed.


(* ----------------------------------------------------------------- *)
(*                   map fst/snd instead of split                    *)
(* ----------------------------------------------------------------- *)

Section Mapsel.
Variable U V: Type.

Lemma mapsel_combine: forall (l: list (U * V)),
  combine (map fst l) (map snd l) = l.
Proof. elim=> // - [l e] G' /= -> //. Qed.

Lemma combine_mapfst: forall (l: list U) (m: list V),
  length l = length m -> map fst (combine l m) = l.
Proof.
  elim=> // a l IH m. case: m=> //= b m H.
  injection H. move/IH=> -> //.
Qed.

Lemma combine_mapsnd: forall (l: list U) (m: list V),
  length l = length m -> map snd (combine l m) = m.
Proof.
  elim=> [| a l IH] m; case: m=> //= b m H.
  injection H. move/IH=> -> //.
Qed.

End Mapsel.


(* ----------------------------------------------------------------- *)
(*                   Conditions btwn head and tail                   *)
(* ----------------------------------------------------------------- *)

Section Memoized.
Variable A: Type.
Variable R: A -> list A -> Prop.

Inductive Memoized: list A -> Prop :=
  | Memoized_nil: Memoized []
  | Memoized_cons: forall a l, R a l -> Memoized l -> Memoized (a :: l)
.

Property Memoized_inv: forall a l, Memoized (a :: l) -> R a l.
Proof. move=> a l H. by inversion H; subst. Qed.

Property Memoized_inv_tail: forall a l, Memoized (a :: l) -> Memoized l.
Proof. move=> a l H. by inversion H; subst. Qed.

End Memoized.

Add Parametric Morphism A: (@Memoized A)
  with signature equiv ==> eq ==> iff as memoize_mor.
Proof.
  move=> R S E l. do 4 red in E. split.
  all: elim=> [|a l' Hh Ht IH]; constructor=> //; apply/E=> //.
Qed.


Section Memoizedb.
Variable A: Type.
Variable R: A -> list A -> bool.

Fixpoint Memoizedb (l: list A): bool :=
  match l with
  | [] => true
  | a :: l' => R a l' && Memoizedb l'
  end.

Property MemoizedP: forall l, reflect (Memoized R l) (Memoizedb l).
Proof.
  move=> l. apply: Bool.iff_reflect. split.
  - elim=> //= a l' Hh _ IH. apply/andP=> //.
  - elim: l=> [_ | a l' IH /= /andP [Hh Ht]]; constructor=> //.
    by apply: IH.
Qed.

End Memoizedb.

(* ----------------------------------------------------------------- *)
(*                        Boolean form of in                         *)
(* ----------------------------------------------------------------- *)

(* only nat version for now *)
Module NatB <: Orders.TotalTransitiveLeBool.
Include Nat.

Lemma leb_total: forall x y, x <=? y \/ y <=? x.
Proof. move=> x y. rewrite /is_true !leb_le. lia. Qed.

Lemma leb_trans: Transitive leb.
Proof. move=> x y z. rewrite /is_true !leb_le. lia. Qed.

Lemma ltb_trans: Transitive ltb.
Proof. move=> x y z. rewrite /is_true !ltb_lt. lia. Qed.


Definition Inb n l := existsb (fun n' => n' =? n) l.

Lemma InP: forall n l, reflect (In n l) (Inb n l).
Proof.
  move=> n l. apply/Bool.iff_reflect. elim: l=> //= a l' IH.
  case: (Nat.eqb_spec a n)=> [->|?] /=. firstorder.
  rewrite IH. firstorder.
Qed.

Definition inclb l m := forallb (fun n => Inb n m) l.

Lemma inclP: forall l m, reflect (incl l m) (inclb l m).
Proof.
  move=> l m. apply/Bool.iff_reflect.
  have ->: incl l m <-> Forall (fun n => In n m) l
    by rewrite /incl Forall_forall //.
  elim: l=> //= n l' IH.
  have ->: n :: l' = [n] ++ l' by done.
  rewrite Forall_app Forall_single IH.
  case: (InP n m)=> /=; firstorder. discriminate.
Qed.

End NatB.

*)