(* ----------------------------------------------------------------- *)
(*                      Basic Category Theory                        *)
(* ----------------------------------------------------------------- *)

From Practice Require Import Base Graph.
From mathcomp Require Export tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.


(* ----------------------------------------------------------------- *)
(*                     Insignificant Morphism                        *)
(* ----------------------------------------------------------------- *)




(* Module NatSort := Sort NatB. *)

Module Type HasSCat (Import T: Equalities.Typ).
Parameter R: t -> t -> Prop.
Axiom PO: PreOrder R.
End HasSCat.
Module Type SCat := Equalities.Typ <+ HasSCat.


Module SDiag (Import M: SCat).

Definition U := M.t.

Section Env1.
Variable T: finType.
Variable V: T -> U.

Definition hold (r: rel T) :=
  forall m n, r m n -> R (V m) (V n).

Lemma hold_trans: forall r, hold r -> hold (connect r).
Proof.
  have PO := PO.
  move=> r H x y. move/connectP=> [p + ->].
  elim: p x=> [| z p' IH] /= x.
  - reflexivity.
  - move/andP=> [Hr /IH]. apply: transitivity. by apply /H.
Qed.

End Env1.

Section Env2.
Variable T S: finType.
Variable W: S -> U.
Variable f: T -> S.

Lemma hold_embed: forall r, hold (W \o f) r -> hold W (relim f r).
Proof.
  move=> r H a' b' /=.
  move=> /existsP [a /andP [Ha]].
  move=> /existsP [b /andP [Hb]].
  move: Ha Hb. rewrite /in_mem /=.
  move/eqP <-. move/eqP <-.
  by move/H.
Qed.

Lemma hold_preim: forall r, hold W r -> hold (W \o f) (relpre f r).
Proof. move=> r H a b /=. by move/H. Qed.

End Env2.

(*
PROBLEM: Relation cannot be evaluated!

Local Example ex_hold_move: forall (a b c d: U),
  hold (tnth [tuple a; b; c])
    (grel (tnth [tuple [:: inord 1]; [:: inord 2]; [::]]))
  -> hold (tnth [tuple a; c; b; d])
    (grel (tnth [tuple [:: inord 1]; [:: inord 1]; [::]; [::]])).
Proof.
  move=> a b c d. move /hold_trans.
  move /(hold_embed (f := tnth [tuple (inord 1); (inord 3); (inord 2)])).
  move /hold_trans.
Qed.
*)

End SDiag.


(*
(* Simple labeled diagram with insignificant morphisms *)
Module SDiag (Import M: SCat).

Definition U := M.t.

(* A diagram holds iff arrows from current node holds and remaining subdiagram holds *)
Inductive Hold (d: U): list U -> DAG.t -> Prop :=
  | Hold_nil: Hold d [] []
  | Hold_cons: forall a e l G, Forall (fun n => R a (rth n l d)) e ->
    Hold d l G -> Hold d (a :: l) (e :: G)
.

Property Hold_inv: forall d a e l G,
  Hold d (a :: l) (e :: G) -> Forall (fun n => R a (rth n l d)) e /\ Hold d l G.
Proof. move=> d a e l G H. inversion H; subst. done. Qed.

Property hold_len: forall d l G, Hold d l G -> length l = length G.
Proof. move=> d l G. elim=> //= a e {}l {}G Hh Ht IH. by f_equal. Qed.


(* TODO simplify *)
Property hold_edge: forall d l G, DAG.DAGF G ->
  Hold d l G <-> length l = length G /\
  forall m n, DAG.hasEdge G m n -> R (rth m l d) (rth n l d).
Proof with eauto.
  move=> d l G DAGF. split.
  - (* -> *)
    move=> H. split. apply: hold_len... move=> m n HasE.
    have {}DAGF : n < m < length G.
    { split. apply: DAG.DAG_edge... apply: DAG.hasEdge_valid... }

    elim: H HasE DAGF=> [| a e l' G' Hh Ht IH] /=. lia.
    move=> HasE Lnm. have Lm: m <= length G' by lia.
    rewrite /DAG.hasEdge in HasE. have {}Ht := (hold_len Ht).

    case: (Lt.le_lt_or_eq _ _ Lm) HasE=> {Lm} [Lm|->].
    + rewrite /DAG.edge !rth_tl //; try lia. move=> ?. apply: IH=> //. lia.
    + rewrite /DAG.edge -{2}Ht !rth_hd rth_tl => {IH}. lia. move=> {Lnm}.
      move: n. by apply /Forall_forall.

  - (* <- *)
    move=> [Len H].
    elim: DAGF l Len H=> [| e G' Hh Ht IH] [| a l'] //=. constructor.
    move=> [Len] H.  have {}IH := (IH _ Len).

    constructor.
    + apply/Forall_forall=> n Hn. move: (H (length l') n).
      rewrite rth_hd /DAG.hasEdge /DAG.edge Len rth_hd=> /(_ Hn).
      rewrite rth_tl // Len. move: n Hn.
      by apply /Forall_forall /(Sorted_extends trans_gt).
    + apply: IH=> m n HasE. move: (H m n).
      have Lm := (DAG.hasEdge_valid HasE).
      have Ln := (DAG.DAG_edge Ht HasE).
      rewrite /DAG.hasEdge /DAG.edge !rth_tl; try lia.
      move=> /(_ HasE) //.
Qed.

Lemma hold_incl: forall d l G K,
  DAG.DAGF G -> DAG.DAGF K -> DAG.Incl G K -> Hold d l K -> Hold d l G.
Proof.
  move=> d l G K HG HK HI. rewrite !hold_edge //.
  have Len := Forall2_len HI. have {}HI := DAG.Incl_edge HI.
  firstorder. lia.
Qed.

(*
Lemma hold_add_empty: forall d l G N, Hold d l G -> Hold d l (repeat [] N ++ G).
Proof. move=> d l G + H. elim=> //= N' IH. constructor=> //. by apply: IH. Qed.
*)


Proposition hold_transCl: forall d l G,
  Hold d l G -> Hold d l (DAG.transClosure G).
Proof.
  move=> d l G. elim=> [| a e l' G' Hh Ht IH] /=; constructor=> //.
  apply /Forall_forall=> n.
  move=> /filter_In []. rewrite -in_rev => /in_seq [_ /= Ln].
  move=> /existsb_exists [s [Hs]].

  move/orP=> [/Nat.eqb_spec -> | /NatB.InP Hn].
  - move: s Hs. by apply /Forall_forall.
  - move: M.Tr=> Tr. transitivity (rth s l' d).
    + move=> {Hn}. move: s Hs. by apply /Forall_forall.
    + move: IH. rewrite hold_edge. move=> [_ +]. by apply. apply: DAG.transCl_DAG.
Qed.

Proposition hold_extend: forall d L tar N l G,
  Sorted gt (N :: tar) -> length tar = length G ->
  l = map (fun m => rth m L d) tar ->
  DAG.DAGF G -> Hold d l G -> Hold d L (DAG.extend N tar G).
Proof.
  move=> d L tar + _ G + + ->.
  elim: tar G=> [|n tar' IH] [|e G'] N //. {
    admit.
    (*
    rewrite /= -(app_nil_r (repeat [] N)) => _ _ _ _.
    apply: hold_add_empty. constructor.
    *)
  }
  
  move=> OrdT. move: (Sorted_inv OrdT)=> [{}OrdT /HdRel_iff Ln].
  move=> [EqL] DAGF.
  have OrdE := Memoized_inv DAGF. have {}DAGF := Memoized_inv_tail DAGF.
  have {}IH := (IH _ _ OrdT EqL DAGF). move=> {DAGF}.

  move=> /= /Hold_inv [Hh Ht].

  (* Conditioning on L.. *)

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
*)




