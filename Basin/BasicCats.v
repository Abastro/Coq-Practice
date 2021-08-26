(* ----------------------------------------------------------------- *)
(*                      Basic Category Theory                        *)
(* ----------------------------------------------------------------- *)

From Practice Require Import Basin.Base.

Import Bool.
Import List.
Import ListNotations.

From Coq Require Import Sorting.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.


(* ----------------------------------------------------------------- *)
(*                     Insignificant Morphism                        *)
(* ----------------------------------------------------------------- *)

Lemma forallb_impl: forall T (f g: T -> bool) l,
  (forall a, f a -> g a) -> forallb f l -> forallb g l.
Proof.
  move=> T f g l H. rewrite /is_true !forallb_forall -!Forall_forall.
  by apply Forall_impl.
Qed.

Lemma forallb_filter: forall T (f g: T -> bool) l,
  forallb f l -> forallb f (filter g l).
Proof.
  move=> T f g l. rewrite /is_true !forallb_forall=> + ?.
  move=> + /filter_In [HI _]. by move/(_ _ HI).
Qed.


Fixpoint LocalRel {T} (r: T -> T -> bool) (l: list T): bool :=
  match l with
  | [] => true
  | x :: l' => if l' isn't x' :: _ then true
    else r x x' && LocalRel r l'
  end.

Property LocalRel_iff: forall T (r: T -> T -> bool) l, Sorted r l <-> LocalRel r l.
Proof.
  move=> T r l. split.
  - (* -> *)
    elim=> [| a l' H1 IH H2] //.
    inversion H2; subst. done. by apply/andP.
  - (* <- *)
    elim: l => [|a l'] //.
    case: l' => [|a' l''] IH. by constructor.
    move/andP => [H1]. move/IH => H2. by constructor; [|constructor].
Qed.
Property LocalRelP: forall T (r: T -> T -> bool) l, reflect (Sorted r l) (LocalRel r l).
Proof. move=> >. apply/iff_reflect /LocalRel_iff. Qed.

Lemma LocalRel_app: forall T (r: T -> T -> bool) l m d1 d2,
  LocalRel r l -> LocalRel r m -> r (last l d1) (hd d2 m) -> LocalRel r (l ++ m).
Proof.
  move=> T r l m ? ?. rewrite -!LocalRel_iff => Hl Hm.
  elim: Hl=> [|a l' Hl' IH Hh] Hr //.
  have ->: ((a :: l') ++ m = a :: (l' ++ m)) by done.
  move: Hh Hl' IH Hr=> [|a' l'' Hh] Hl' IH Hr.
  - constructor=> // {Hm Hl' IH}.
    by case: m Hr=> [|? ?] Hr; constructor.
  - constructor. apply /IH /Hr. by constructor.
Qed.

Lemma LocalRel_map: forall S T (rS: S -> S -> bool) (rT: T -> T -> bool) (f: S -> T) l,
  (forall s s', rS s s' -> rT (f s) (f s')) -> LocalRel rS l -> LocalRel rT (map f l).
Proof.
  move=> S T rS rT f l H. rewrite -!LocalRel_iff.
  elim => [| a l' HS HT Hh] /=; constructor=> // {HS HT}.
  case: Hh => [|a' l'' HS]; constructor. apply /H /HS.
Qed.
Corollary LocalRel_impl: forall T (r1: T -> T -> bool) (r2: T -> T -> bool) l,
  (forall t t', r1 t t' -> r2 t t') -> LocalRel r1 l -> LocalRel r2 l.
Proof.
  move=> T r1 r2 l Im.
  suff: LocalRel r1 l -> LocalRel r2 (map id l) by rewrite map_id.
  by apply: LocalRel_map.
Qed.

Lemma LocalRel_filter: forall T (r: T -> T -> bool) (p: T -> bool) l,
  Transitive r -> LocalRel r l -> LocalRel r (filter p l).
Proof.
  move=> T r p l Tr. rewrite -!LocalRel_iff.
  move/(Sorted_StronglySorted Tr) => H. apply: StronglySorted_Sorted.
  elim: H=> [| a l' Hl IH HA]. by constructor.
  simpl. case: (p a) => //.
  constructor=> //.
  apply/incl_Forall; by [apply: incl_filter|].
Qed.


Module NatB <: Orders.TotalTransitiveLeBool.
Include Nat.

Lemma leb_total: forall x y, x <=? y \/ y <=? x.
Proof. move=> x y. rewrite /is_true !leb_le. lia. Qed.

Lemma leb_trans: Transitive leb.
Proof. move=> x y z. rewrite /is_true !leb_le. lia. Qed.

Lemma ltb_trans: Transitive ltb.
Proof. move=> x y z. rewrite /is_true !ltb_lt. lia. Qed.

End NatB.
Module NatSort := Sort NatB.


Lemma sorted_seq: forall m n, LocalRel Nat.ltb (seq m n).
Proof.
  move=> m n. apply/LocalRel_iff. move: m.
  elim: n => [| n' IH] m /=; constructor=> // {IH}.
  case: n' => [| n'']; constructor.
  apply/Nat.ltb_lt. lia.
Qed.


(* Represents a graph, wth the outer list indices given in reverse (e.g. 3; 2; 1). *)
Definition PGraph := list (list nat).


(* Pairs with mergesort *)
Definition GraphSorted (G: PGraph): bool := forallb (LocalRel Nat.leb) G.
Lemma sort_then_sorted: forall G, GraphSorted (map NatSort.sort G).
Proof.
  move=> G. apply/forallb_forall => e. move/in_map_iff => {e} [e [<- H]].
  apply/LocalRelP /NatSort.Sorted_sort.
Qed.

Definition GraphUniq (G: PGraph): bool := forallb (LocalRel (fun x y => ~~(x =? y))) G.
Definition GraphBnd (G: PGraph): bool := forallb (forallb (fun n => n <? length G)) G.

Property GraphBnd_In: forall G e n,
  GraphBnd G -> In e G -> In n e -> n < length G.
Proof.
  move=> G e n + He Hn. rewrite /GraphBnd.
  move /forallb_forall /(_ _ He).
  move /forallb_forall /(_ _ Hn).
  by move /Nat.ltb_lt.
Qed.


Definition Inb (n: nat) (l: list nat) := existsb (fun n' => n' =? n) l.
Definition EdgeFrom (G: PGraph) (m: nat) := nth m (rev G) [].
Definition HasEdge (G: PGraph) (m: nat) (n: nat) := Inb n (EdgeFrom G m).

Definition GraphDAG (G: PGraph): bool :=
  forallb (fun m => forallb (fun n => n <? m) (EdgeFrom G m)) (seq 0 (length G)).


Lemma InbP: forall n l, reflect (In n l) (Inb n l).
Proof.
  move=> n l. apply/iff_reflect. elim: l=> //= a l' IH.
  case: (Nat.eqb_spec a n)=> [->|?] /=. firstorder.
  rewrite IH. firstorder.
Qed.


Lemma EdgeFrom_tl: forall e G m,
  m < length G -> EdgeFrom (e :: G) m = EdgeFrom G m.
Proof.
  move=> e G m. rewrite /EdgeFrom /= -rev_length. apply: app_nth1.
Qed.

Lemma EdgeFrom_hd_or_tl: forall e G m,
  m <= length G -> EdgeFrom (e :: G) m = e \/ EdgeFrom (e :: G) m = EdgeFrom G m.
Proof.
  move=> e G m. rewrite /EdgeFrom /= -rev_length.
  case/Lt.le_lt_or_eq=> [Hm | ->].
  - right. by apply: app_nth1.
  - left. rewrite app_nth2. lia. by rewrite Nat.sub_diag.
Qed.

Lemma EdgeFrom_in_or_nil: forall m G,
  {In (EdgeFrom G m) G} + {EdgeFrom G m = []}.
Proof.
  move=> m G. rewrite /EdgeFrom.
  case: (nth_in_or_default m (rev G) [])=> [|->]; [left | by right].
  by apply/in_rev.
Qed.

Property GraphDAG_In: forall G m n,
  GraphDAG G -> In n (EdgeFrom G m) -> n < m.
Proof.
  move=> G m n + Hn. rewrite /GraphDAG.
  have Hm: In m (seq 0 (length G)). {
    apply/in_seq. split=> /=. lia.
    case: (Nat.le_gt_cases (length G) m)=> Hm //. move: Hn.
    rewrite -rev_length in Hm. rewrite /EdgeFrom nth_overflow //.
  }
  move/forallb_forall /(_ _ Hm).
  move/forallb_forall /(_ _ Hn).
  by move/Nat.ltb_spec0.
Qed.


Definition GraphTrans (G: PGraph): bool :=
  forallb (fun e =>
    forallb (fun n =>
      forallb (fun k => Inb k e) (EdgeFrom G n)
    ) e
  ) G.

Lemma GraphTrans_transitive: forall G m n k,
  GraphTrans G -> HasEdge G m n -> HasEdge G n k -> HasEdge G m k.
Proof.
  move=> G m n k.
  rewrite /GraphTrans /HasEdge.
  case: (EdgeFrom_in_or_nil m G)=> [HI|->] //.
  move=> /forallb_forall /(_ _ HI) => {HI} + /InbP Hn.
  move=> /forallb_forall /(_ _ Hn)=> {Hn} + /InbP Hk.
  move=> /forallb_forall /(_ _ Hk)=> +. done.
Qed.


(* Transitivie closure of the graph *)
Fixpoint transClosure (G: PGraph): PGraph :=
  match G with
  | [] => []
  | e :: G' => let Cl := transClosure G' in
    filter (fun k => existsb (fun n => (k =? n) || HasEdge Cl n k) e) (seq 0 (length G))
    :: Cl
  end.

Local Example ex_transClosure: transClosure [[1]; [0]; []] = [[0; 1]; [0]; []].
Proof. reflexivity. Qed.

Property transCl_len: forall G, length (transClosure G) = length G.
Proof. elim=> [| e G' IH] //=. by rewrite IH. Qed.

Lemma transCl_str_sorted: forall G, forallb (LocalRel Nat.ltb) (transClosure G).
Proof.
  elim=> [| e G' IH] //.
  rewrite /transClosure -/transClosure [seq]lock /= -lock.
  apply/andP. split=> //.
  apply: LocalRel_filter. apply: NatB.ltb_trans. apply: sorted_seq.
Qed.

Lemma transCl_uniq: forall G, GraphUniq (transClosure G).
Proof.
  rewrite /GraphUniq => G.
  have := transCl_str_sorted G.
  apply: forallb_impl=> ?. apply: LocalRel_impl=> t t'.
  move/Nat.ltb_lt => H. case: (Nat.eqb_spec t t') => //; lia.
Qed.

Lemma transCl_sorted: forall G, GraphSorted (transClosure G).
Proof.
  rewrite /GraphSorted => G.
  have := transCl_str_sorted G.
  apply: forallb_impl=> ?. apply: LocalRel_impl=> t t'.
  move/Nat.ltb_lt=> H. apply/Nat.leb_le. lia.
Qed.

Lemma transCl_bnd: forall G, GraphBnd (transClosure G).
Proof.
  elim=> [| e G'] //.
  rewrite /GraphBnd /transClosure -/transClosure.
  rewrite [seq]lock /= -lock !transCl_len.
  move=> IH. apply/andP. split.
  - move=> {IH}.
    apply /forallb_filter /forallb_forall=> ?.
    move/in_seq=> [_ ?]. by apply/Nat.ltb_lt.
  - move: IH.
    do 2 apply: forallb_impl=> ?.
    move/Nat.ltb_lt=> ?. apply/Nat.ltb_lt. lia.
Qed.

(* Lemma transCl_DAG: forall G, GraphDAG G -> GraphDAG (transClosure G).
Proof.
  elim=> [| e G'] // IH H.
  rewrite /GraphDAG transCl_len.
  rewrite /transClosure -/transClosure.
  
  {1}[seq]lock /=.
  apply/andP. split.
  - (* Head *)
    apply/forallb_forall=> n. rewrite /EdgeFrom.
    move /filter_In=> []. move /in_seq=> [_ /= Hn].
    move /existsb_exists=> [k Hk].
    apply /forallb_filter /forallb_forall => n.
    move /in_seq=> [_ /= ?]. apply /Nat.ltb_spec0. lia.
    rewrite /is_true forallb_forall. *)


Theorem transCl_transitive: forall G, GraphTrans (transClosure G).
Proof.
  elim=> [| e G'] // IH.
  rewrite /GraphTrans.
  rewrite /transClosure -/transClosure [seq]lock /= -lock.
  set Hd := filter (fun k : nat => existsb
     (fun n : nat => (k =? n) || HasEdge (transClosure G') n k) e) (seq 0 (S (length G'))).
  apply/andP. split.

  - (* Head part *)
    apply/forallb_forall=> n.
    move/filter_In=> []. move/in_seq=> [_ /= En].
    move/existsb_exists=> [m [Hme Hm]].

    apply /forallb_forall=> k Hk. apply /InbP. move: Hk.
    have {} En: n <= length (transClosure G'). { rewrite transCl_len. lia. }
    case: (EdgeFrom_hd_or_tl Hd En) => -> // Hk.
    apply/filter_In. split.

    + (* k in seq 0 (len G) *)
      apply/in_seq. split. lia.
      suff: k < length G' by lia. rewrite -transCl_len.
      case: (EdgeFrom_in_or_nil n (transClosure G')) Hk => [|->] //.
      apply: GraphBnd_In; eauto. apply: transCl_bnd.

    + (* Has edge through the closure *)
      apply/existsb_exists. exists m. split=> // {Hme}.
      apply/orP. right.
      move: Hk Hm => /InbP Hk /orP [|Hm].
      by move/Nat.eqb_spec=> <-.
      apply: GraphTrans_transitive=> //; eauto.

  - (* Tail part - Inductive *)
    move: IH. rewrite /GraphTrans /is_true.
    rewrite !forallb_forall=> + f Hf. move/(_ _ Hf).
    rewrite !forallb_forall=> + n Hn. move/(_ _ Hn).
    rewrite EdgeFrom_tl=> // {Hd e}.
    apply: GraphBnd_In; eauto. apply: transCl_bnd.
Qed.

(* Transitive closure DAG *)
Record ClDAG := mkClDAG{
  cldag_edges: PGraph
; cldag_cond: true =
  GraphSorted cldag_edges
  && GraphUniq cldag_edges
  && GraphBnd cldag_edges
  && GraphDAG cldag_edges
  && GraphTrans cldag_edges
}.



End.

