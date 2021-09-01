(* ----------------------------------------------------------------- *)
(*                       Simple finite Graphs                        *)
(* ----------------------------------------------------------------- *)

From Practice Require Import Basin.Base.
From Practice Require Import Basin.ListPlus.

Import List.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.


(* Directed graph represented with Nat *)
Module DGraph <: Equalities.Typ.

Definition t := list (list nat).

Definition WForm (G: t): Prop :=
  Forall (fun e => Sorted gt (length G :: e)) G.

Definition WFormb (G: t): bool :=
  forallb (fun e => Sortedb (flip Nat.ltb) (length G :: e)) G.

Property WFP: forall G, reflect (WForm G) (WFormb G).
Proof.
  move=> G. apply: Bool.iff_reflect. rewrite /WForm /WFormb is_true_fold.
  rewrite -rwP; [| apply/ForallP]. apply: Forall_mor=> // e.
  rewrite -rwP; [| apply/SortedP]. apply: Sorted_mor=> // n m.
  rewrite /flip /is_true Nat.ltb_lt //.
Qed.

Definition edge (G: t) (n: nat) := rth n G [].
Definition hasEdge (G: t) (m: nat) (n: nat) := In n (edge G m).

Lemma hasEdge_valid: forall (G: t) m n,
  hasEdge G m n -> m < length G.
Proof.
  move=> G m n.
  case: (Nat.le_gt_cases (length G) m)=> Hm //.
  rewrite /hasEdge /edge rth_overflow //.
Qed.


(* Is G included in G' ? *)
Definition Incl (G K: t): Prop :=
  Forall2 (@incl nat) G K.

Definition Inclb (G K: t): bool :=
  forall2b (NatB.inclb) G K.

Property InclP: forall G K, reflect (Incl G K) (Inclb G K).
Proof.
  move=> G K. apply: Bool.iff_reflect. rewrite /Incl /Inclb is_true_fold.
  rewrite -rwP; [| apply/Forall2P]. apply: Forall2_mor=> // l m.
  apply: rwP. apply: NatB.inclP.
Qed.

Property Incl_edge: forall G K,
  Incl G K -> forall m, incl (edge G m) (edge K m).
Proof.
  move=> G K HI m n Hn. move: (hasEdge_valid Hn) => Hm.
  move: HI Hn. rewrite /Incl /edge /rth.
  move /Forall2_rev /Forall2_nth=> [_] /(_ m [] []).
  rewrite rev_length /incl=> /(_ Hm n) //.
Qed.


Definition shift (k: nat) (G: t) :=
  map (map (plus k)) G.

End DGraph.


(* Directed Acyclic Graph *)
Module DAG <: Equalities.Typ.
Include DGraph.

Definition DAGF (G: t): Prop :=
  Memoized (fun e G => Sorted gt (length G :: e)) G.

Definition DAGFb (G: t): bool :=
  Memoizedb (fun e G => Sortedb (flip Nat.ltb) (length G :: e)) G.

Property DAGFP: forall G, reflect (DAGF G) (DAGFb G).
Proof.
  move=> G. apply: Bool.iff_reflect. rewrite /DAGF /DAGFb is_true_fold.
  rewrite [cons]lock.
  rewrite -rwP; [| apply: MemoizedP]=> /=. apply: memoize_mor=> // e G'.
  rewrite -rwP; [| apply: SortedP]. apply: Sorted_mor=> // a b.
  apply: rwP. apply: Nat.ltb_spec0.
Qed.


Lemma DAGF_WF: forall G, DAGF G -> WForm G.
Proof.
  move=> G. elim=> //= e G' Hh _ IH. constructor.
  - move: Hh. rewrite !Sorted_inv_Forall.
    move=> [H ?]. split=> //. move: H.
    apply: Forall_impl=> ?. simpl; lia.
  - move: IH. apply: Forall_impl=> ?.
    rewrite !Sorted_inv_Forall. move=> [H ?]. split=> //. move: H.
    apply: Forall_impl=> ?. simpl; lia.
Qed.


Property DAG_edge: forall G,
  DAGF G -> forall m n, hasEdge G m n -> n < m.
Proof.
  move=> G + m n. elim=> [| e G' Hh Ht IH]. case: m n=> //=.
  move=> Hn. have /= Hm := (hasEdge_valid Hn).
  have {}Hm: m <= length G' by lia.
  case: (Lt.le_lt_or_eq _ _ Hm) Hn=> [{}Hm|->].
  - rewrite /hasEdge /edge rth_tl //.
  - rewrite /hasEdge /edge rth_hd. move: (Sorted_extends trans_gt Hh).
    move /Forall_forall /(_ n)=> //.
Qed.


(*
  DAG Extension.
  (N :: tar) should be in decreasing order, with length tar = length G.
*)
Fixpoint extend (N: nat) (tar: list nat) (G: t): t :=
  match tar, G with
  | n :: tar', e :: G' =>
    repeat [] (N - S n) ++ map (fun m => rth m tar 0) e :: extend n tar' G'
  | _, _ => repeat [] N
  end.

Local Example ex_extend: extend 6 [4; 3; 1] [[1]; [0]; []] = [[]; [3]; [1]; []; []; []].
Proof. reflexivity. Qed.


Property extend_len: forall N tar G,
  Sorted gt (N :: tar) -> length (extend N tar G) = N.
Proof.
  move=> N tar G. elim: G N tar=> [|e G' IH] N [|n tar'] H /=.
  all: try apply: repeat_length.
  move: (Sorted_inv H)=> {H} [Ht Hh]. move: (HdRel_inv Hh)=> {}Hh.
  rewrite app_length repeat_length /= IH //. lia.
Qed.


Property extend_DAG: forall N tar G,
  Sorted gt (N :: tar) -> length tar = length G ->
  DAGF G -> DAGF (extend N tar G).
Proof.
  have DAGRep: forall N G, DAGF G -> DAGF (repeat [] N ++ G).
  { elim=> //= n' IH G. repeat constructor. by apply: IH. }

  move=> N tar G. elim: tar N G=> [| n tar' IH] N [| e G'] //=.
  all: move=> OrdT Len FormG; rewrite /WForm.
  rewrite -(app_nil_r (repeat [] N)). by apply: DAGRep.

  (* Hypothesis expand *)
  move: Len=> [Len].
  move: (Sorted_inv OrdT)=> [{}OrdT Hn]. move: (HdRel_inv Hn)=> {}Hn.
  move: (Memoized_inv FormG) (Memoized_inv_tail FormG)=> OrdE {}FormG.
  move: IH=> /(_ _ _ OrdT Len FormG) {}IH {FormG}.
  apply: DAGRep. constructor=> //.

  rewrite extend_len //.
  move: OrdE. rewrite !Sorted_inv_Forall.
  move=> [BndE OrdE]. split.

  (* Showing Expand sort *)
  - apply /Forall_forall=> _ /in_map_iff [m [<-]] Hm.
    move: BndE=> /Forall_forall /(_ _ Hm). rewrite -Len=> {}Hm.
    rewrite rth_tl //. move: Hm=> /(rth_In 0).
    move: (rth m tar' 0). by apply /Forall_forall /(Sorted_extends trans_gt).

  - set f := fun m => rth m (n :: tar') 0.
    apply /(Sorted_nth _ (f 0) (f 0)).
    rewrite map_length=> s s' H. rewrite !map_nth /f /rth.
    move: OrdT=> /Sorted_rev /Sorted_nth. apply.
    rewrite rev_length /=. split.
    move: OrdE=> /Sorted_nth. by apply.
    suff: nth s e 0 < length G' by lia.
    move: BndE=> /Forall_nth. apply. lia.
Qed.


(* Is a graph transitive? *)
Definition isTrans (G: t): bool :=
  forallb (fun e =>
    forallb (fun n =>
      forallb (fun k => NatB.Inb k e) (edge G n)
    ) e
  ) G.

Lemma isTrans_transitive: forall G,
  isTrans G <-> Transitive (hasEdge G).
Proof.
  move=> G. split.
  - (* -> *)
    move=> + m n k. rewrite /isTrans /hasEdge /edge.
    case: (rth_in_or_def G m []) => [HI|->] //.
    move=> /forallb_forall /(_ _ HI) => {HI} + Hn.
    move=> /forallb_forall /(_ _ Hn)=> {Hn} + Hk.
    move=> /forallb_forall /(_ _ Hk) /NatB.InP. done.
  - (* <- *)
    rewrite /isTrans /hasEdge. move=> Tr.
    apply /forallb_forall=> e /(In_rth []) - [m [Hm <-]].
    apply /forallb_forall=> n Hn.
    apply /forallb_forall=> k Hk.
    apply /NatB.InP /Tr; eauto.
Qed.


(* For now, transitive closure calculation reside here *)
(* Transitivie closure of the graph *)
Fixpoint transClosure (G: t): t :=
  match G with
  | [] => []
  | e :: G' => let Cl := transClosure G' in
    filter (fun k => existsb (fun n => (k =? n) || NatB.Inb k (edge Cl n)) e)
      (rev (seq 0 (length G')))
    :: Cl
  end.

Local Example ex_transClosure: transClosure [[1]; [0]; []] = [[1; 0]; [0]; []].
Proof. reflexivity. Qed.

Property transCl_len: forall G, length (transClosure G) = length G.
Proof. elim=> [| e G' IH] //=. by rewrite IH. Qed.

(* Always a DAG *)
Property transCl_DAG: forall G, DAGF (transClosure G).
Proof.
  elim=> [|e G' IH] /=; constructor=> //.
  rewrite transCl_len. rewrite Sorted_inv_Forall. split.
  - apply: incl_Forall. apply: incl_filter.
    apply /Forall_rev /Forall_forall=> n /in_seq [] //.
  - apply /Sorted_filter /Sorted_rev /Sorted_seq.
Qed.


Property transCl_transitive: forall G, isTrans (transClosure G).
Proof.
  elim=> // e G'. rewrite !isTrans_transitive /hasEdge => IH.
  move=> m n k Hn Hk.
  have Lknm: k < n < m. {
    move: (transCl_DAG (e :: G'))=> /DAG_edge DAG.
    by move: Hn Hk=> /DAG + /DAG.
  }
  have Leq: m <= length (transClosure G').
  { move: Hn=> /hasEdge_valid /=. lia. }

  move: Hn Hk=> /=.
  set Hd := filter (fun k =>
    existsb (fun n => (k =? n) || NatB.Inb k (edge (transClosure G') n)) e)
    (rev (seq 0 (length G'))).
  case: (Lt.le_lt_or_eq _ _ Leq)=> [{}Leq | ->].

  - (* Tail part, recursive *)
    rewrite /edge !rth_tl //. lia. apply: IH.

  - (* Head part *)
    rewrite /edge rth_hd rth_tl. lia.
    move=> /filter_In [_] /existsb_exists [s [Hs]].
    move=> /orP[/Nat.eqb_spec -> | /NatB.InP Hn] Hk.
    all: apply /filter_In.
    all: rewrite -in_rev -transCl_len.
    all: split; [apply /in_seq; lia| ].
    all: apply /existsb_exists; exists s; split=> //.
    all: apply /orP; right. all: apply /NatB.InP.
    done. apply: IH; eauto.
Qed.

End DAG.
