(* ----------------------------------------------------------------- *)
(*                      Basic Category Theory                        *)
(* ----------------------------------------------------------------- *)

From Practice Require Import Basin.Base.
From Practice Require Import Basin.ListPlus.
From Practice Require Import Basin.Graph.

Import List.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.


(* ----------------------------------------------------------------- *)
(*                     Insignificant Morphism                        *)
(* ----------------------------------------------------------------- *)

(* Module NatSort := Sort NatB. *)


Module Type HasSCat (Import T: Equalities.Typ).
Parameter R: t -> t -> Prop.
Axiom Tr: Transitive R.
End HasSCat.
Module Type SCat := Equalities.Typ <+ HasSCat.


(* Simple labeled diagram with insignificant morphisms *)
Module SDiag (Import M: SCat).

Definition U := M.t.

(* TODO Perhaps double is easier *)
Definition Hold (d: U) (l: list U) (G: DAG.t): Prop :=
  Memoized (fun e G' => Forall (fun n => R (rth (length G') l d) (rth n l d)) e) G.


(* A diagram holds iff arrows from current node holds and remaining subdiagram holds *)
(*
Inductive Hold (d: U): list U -> DAG.t -> Prop :=
  | Hold_nil: Hold d [] []
  | Hold_cons: forall a l e G, Forall (fun n => R a (rth n l d)) e ->
    Hold d l G -> Hold d (a :: l) (e :: G)
.

Property Hold_inv: forall d l e G,
  Hold d (a :: l) (e :: G) -> Forall (fun n => R l (rth n (labels G) d)) e /\ Hold d l G.
Proof. move=> d l e G H. inversion H; subst. done. Qed.
*)



Property hold_edge: forall d l G, DAG.DAGF G ->
  Hold d l G <->
  forall m n, DAG.hasEdge G m n -> R (rth m l d) (rth n l d).
Proof with eauto.
  move=> d l G DAGF. split.
  - (* -> *)
    move=> H m n HasE.
    have {}DAGF : n < m < length G.
    { split. apply: DAG.DAG_edge... apply: DAG.hasEdge_valid... }

    elim: H HasE DAGF => [| e G' Hh _ IH] /=. lia.
    move=> HasE Lnm. have Lm: m <= length G' by lia.
    rewrite /DAG.hasEdge in HasE.

    case: (Lt.le_lt_or_eq _ _ Lm) HasE=> {Lm} [Lm|->].
    + rewrite /DAG.edge rth_tl // => ?. apply: IH=> //. lia.
    + rewrite /DAG.edge rth_hd => {IH Lnm}.
      move: n. by apply /Forall_forall.

  - (* <- *)
    elim: DAGF=> [|e G' Hh Ht IH] H; constructor.
    + apply/Forall_forall=> n Hn. apply: H.
      rewrite /DAG.hasEdge /DAG.edge rth_hd //.
    +  apply: IH=> m n HasE. apply: H.
      rewrite /DAG.hasEdge /DAG.edge rth_tl //.
      apply: DAG.hasEdge_valid...
Qed.

Lemma hold_incl: forall d l G K,
  DAG.DAGF G -> DAG.DAGF K -> DAG.Incl G K -> Hold d l K -> Hold d l G.
Proof.
  move=> d l G K HG HK. rewrite !hold_edge //.
  move/DAG.Incl_edge. firstorder.
Qed.

Lemma hold_add_empty: forall d l G N, Hold d l G -> Hold d l (repeat [] N ++ G).
Proof. move=> d l G. elim=> //= N' IH H. constructor=> //. by apply: IH. Qed.


Proposition hold_transCl: forall d l G,
  Hold d l G -> Hold d l (DAG.transClosure G).
Proof.
  move=> d l G. elim=> [| e G' Hh Ht IH] /=; constructor=> //.
  apply /Forall_forall=> n.
  move=> /filter_In []. rewrite -in_rev => /in_seq [_ /= Ln].
  move=> /existsb_exists [s [Hs]].

  rewrite DAG.transCl_len.
  move/orP=> [/Nat.eqb_spec -> | /NatB.InP Hn].
  - move: s Hs. by apply /Forall_forall.
  - move: M.Tr=> Tr. transitivity (rth s l d).
    + move=> {Hn}. move: s Hs. by apply /Forall_forall.
    + move: IH. rewrite hold_edge. by apply. apply: DAG.transCl_DAG.
Qed.

Proposition hold_extend: forall d L tar N l G,
  Sorted gt (N :: tar) -> length tar = length G ->
  l = map (fun m => rth m L d) tar ->
  DAG.DAGF G -> Hold d l G -> Hold d L (DAG.extend N tar G).
Proof.
  move=> d L tar + _ G + + ->.
  elim: tar G=> [|n tar' IH] [|e G'] N //. {
    rewrite /= -(app_nil_r (repeat [] N)) => _ _ _ _.
    apply: hold_add_empty. constructor.
  }
  
  move=> OrdT. move: (Sorted_inv OrdT)=> [{}OrdT /HdRel_iff Ln].
  move=> [EqL] DAGF.
  move: (Memoized_inv DAGF) (Memoized_inv_tail DAGF)=> OrdE {}DAGF.
  have {}IH := (IH _ _ OrdT EqL DAGF). move=> {DAGF}.

  move=> H. move: (Memoized_inv H) (Memoized_inv_tail H)=> {H} Hh Ht.

  simpl. apply: hold_add_empty. constructor.
  - rewrite DAG.extend_len //.
    apply /Forall_forall=> _ /in_map_iff [+ [<-]]. apply /Forall_forall.
    move: OrdE=> /Sorted_inv_Forall [+ _].
    move/(Forall_and Hh). apply: Forall_impl=> m [+ Lm].
    congr R.
    + rewrite /= rth_hd2 // map_length //.
    + pose f s := rth s L d.
      rewrite -/f (rth_indep _ (f 0)). rewrite map_length /=. lia.
      rewrite map_rth //.
  - apply: IH. admit.
Admitted.

End SDiag.




Module NopedOut := Nat.
