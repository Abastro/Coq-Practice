(* ----------------------------------------------------------------- *)
(*                      Basic Category Theory                        *)
(* ----------------------------------------------------------------- *)

From Practice Require Import Base Evaluable Graph Tacs.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.


(* ----------------------------------------------------------------- *)
(*                     Insignificant Morphism                        *)
(* ----------------------------------------------------------------- *)


Module Type HasSCat (Import T: Equalities.Typ).
Parameter R: t -> t -> Prop.
Axiom PO: PreOrder R.
Existing Instance PO.
End HasSCat.
Module Type SCat := Equalities.Typ <+ HasSCat.


Module SDiag (Import M: SCat).

Definition U := M.t.

(* Convenient way to make a graph *)
Definition MkGraph n (t: seq (nat * nat)): graph n :=
  relgraph [rel i j | (nat_of_ord i, nat_of_ord j) \in t].


Section Env1.
Variable n: nat.
Variable V: n.-tuple U.

Definition hold (G: graph n) :=
  forall a b, (grrel G: rel _) a b -> R (tnth V a) (tnth V b).

Lemma hold_trans G: hold G -> hold (transCl G).
Proof.
  move=> H x y. move/transClP=> [p + ->].
  elim: p x=> [| z p' IH] /= x.
  - reflexivity.
  - move/andP=> [Hr /IH]. apply: transitivity. by apply /H.
Qed.

Lemma hold_incl (G K: graph n): grincl G K -> hold K -> hold G.
Proof. move/grincl_rel=> + + x y. move=> /(_ x y) + /(_ x y). firstorder. Qed.

Lemma hold_add (G K: graph n): hold G -> hold K -> hold (gradd G K).
Proof. move=> HG HK a b. rewrite graddK=> /orP [/HG|/HK] //. Qed.

End Env1.


Section Env2.
Variable m n: nat.
Variable W: n.-tuple U.
Variable f: 'I_m -> 'I_n.

Lemma hold_embed G: hold (tupleOf (tnth W \o f)) G -> hold W (graphim f G).
Proof.
  move=> H _ _ /graphim_rel[x [y]] [->] [->].
  move/H. rewrite evals !tnth_mktuple //.
Qed.

Lemma hold_embed_eq G V:
  val V = val (tupleOf (tnth W \o f)) -> hold V G -> hold W (graphim f G).
Proof. move=> /val_inj ->. apply/hold_embed. Qed.

Lemma hold_preim G: hold W G -> hold (tupleOf (tnth W \o f)) (graphpre f G).
Proof.
  move=> H a b /graphpre_rel /H.
  rewrite evals !tnth_mktuple //.
Qed.

Lemma hold_preim_eq G V:
  val V = val (tupleOf (tnth W \o f)) -> hold W G -> hold V (graphpre f G).
Proof. move=> /val_inj ->. apply/hold_preim. Qed.


End Env2.


(* TODO Use Mtac: how with varying term? *)
(* Simplifies the top hold. Use this to view how it is currently *)
Ltac lhold_simpl := lazymatch goal with
  | [ |- hold _ ?G -> _ ] => 
    let vG := eval compute in (val G) in
    have ->: G = [tuple of vG] by apply/val_inj
  | _ => fail 0 "Top assumption should be 'hold'"
  end.

(* Apply image to the top hold *)
Ltac lhold_to W := lazymatch goal with
  | [ |- hold ?V _ -> _ ] =>
    let f := constr:(eval (mtupmap V W)) in
    move=> /(hold_embed_eq (W := W) (f := f))=> /(_ erefl)
  | _ => fail 0 "Top assumption should be 'hold'"
  end.

(* TODO Better efficiency *)
(* Adds two top hold statements, applying transitive closure *)
Ltac lhold_add := lazymatch goal with
  | [ |- hold ?V ?G -> hold ?W ?K -> _ ] =>
    let E' := eval compute in (eval (mrmdup (V ++ W))) in
    let E := constr:([tuple of E']) in
    let n := fresh "N" in
    lhold_to E=> n;
    lhold_to E;
    move=> /(hold_add n) /hold_trans {n}
  | _ => fail 0 "Top 2 assumptions should be 'hold'"
  end.


Local Example hold_add_ex: forall (a b c d: U),
  hold [tuple a; b] (MkGraph _ [:: (0, 1)]) ->
  hold [tuple b; c] (MkGraph _ [:: (0, 1)]) ->
  hold [tuple a; c; b; d] (MkGraph _ [:: (0, 1); (2, 1)]).
Proof.
  move=> a b c d.
  lhold_add. lhold_to [tuple a; c; b; d].
  by apply/hold_incl.
Qed.


(* Automatically applies hold statements to the inner assumption *)
Ltac lhold_move := lazymatch goal with
  | [ |- (hold ?W ?G) -> (hold ?V ?K -> _) -> _ ] =>
    let H := fresh "H" in
    let N := fresh "N" in
    move=> H;
    let f := constr: (eval (mtupmap V W)) in
    have N := hold_preim_eq (W := W) (V := V) (f := f) erefl H;
    (have {} N: hold V K by move: N; apply/hold_incl);
    move=> /(_ N) {N}; move: H
  | _ => fail 0 "Top assumption should be 'hold'"
    "and second assumption should assume 'hold' with same env"
  end.

Local Example hold_move_ex: forall (a b c: U) (P: U -> Prop),
  hold [tuple a; b; c] (MkGraph _ [:: (0, 1); (1, 2); (2, 1)]) ->
  (hold [tuple b; c] (MkGraph _ [:: (0, 1); (1, 0)]) -> b = c) ->
  P b -> P c.
Proof. move=> a b c P. lhold_move=> _ -> //. Qed.

End SDiag.

