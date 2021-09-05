(* ----------------------------------------------------------------- *)
(*                            Finite Graphs                          *)
(* ----------------------------------------------------------------- *)

From Practice Require Import Base.
From mathcomp Require Export fintype path fingraph finfun.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.


(* Finite version of relation - construct with finrel. *)

Section FinRel.
Variable T: finType.

Variant fnrel :=
  Finrel of {ffun T -> {ffun T -> bool}}.

Local Definition finrel_def (r: rel T): fnrel :=
  Finrel [ffun x => finfun (r x)].

Definition rel_of_fin (r: fnrel): rel T :=
  let: Finrel r' := r in [rel a b | r' a b].
Coercion rel_of_fin: fnrel >-> rel.

End FinRel.


(* Opaque definition *)
Module Type FinrelDefSig.
Parameter finrel : forall (T: finType), rel T -> fnrel T.
Axiom finrelE : finrel = finrel_def.
End FinrelDefSig.

Module FinrelDef : FinrelDefSig.
Definition finrel := finrel_def.
Lemma finrelE : finrel = finrel_def. reflexivity. Qed.
End FinrelDef.

Notation finrel := FinrelDef.finrel.
Canonical finrel_unlock := Unlockable FinrelDef.finrelE.


Section FinRel.
Variable T: finType.

Property fnrelE (r: rel T) a b: (finrel r) a b = r a b.
Proof. rewrite unlock /= !ffunE //. Qed.

Property fnrelP (r1 r2: fnrel T): (forall a b, r1 a b = r2 a b) <-> r1 = r2.
Proof.
  move: r1 r2=> [r1] [r2]. transitivity (r1 = r2).
  rewrite -ffunP /=. split=> H a; by apply/ffunP.
  split. by move ->. by move=> [].
Qed.

Property fnrelK: cancel (@rel_of_fin T) (@finrel T).
Proof. rewrite /cancel=> r. apply /fnrelP /fnrelE. Qed.

End FinRel.


Section Graph.
Variable T: finType.
Variable e: fnrel T.

Definition fnconnect: fnrel T := finrel (connect e).

Property fnconnectP x y:
  reflect (exists2 p, path e x p & y = last x p) (fnconnect x y).
Proof. rewrite /fnconnect fnrelE. apply/connectP. Qed.

Property fnconnect_trans: transitive fnconnect.
Proof.
  rewrite /fnconnect /transitive=> y x z.
  rewrite !fnrelE. apply /connect_trans.
Qed.

Lemma fnconnect0 x: fnconnect x x.
Proof. rewrite /fnconnect fnrelE. apply/connect0. Qed.

Lemma fnconnect1 x y: e x y -> fnconnect x y.
Proof. rewrite /fnconnect fnrelE. apply/connect1. Qed.

(* TODO More Lemmas *)

End Graph.


Section Image.
Variable T S: finType.
Variable f: T -> S.

Definition fnrelpre (r: fnrel S): fnrel T :=
  finrel (relpre f r).

Definition fnrelim (r: fnrel T): fnrel S :=
  finrel [rel a' b' | [
    exists a in preim f (pred1 a'),
    exists b in preim f (pred1 b'),
    r a b
  ] ].


Section InjImage.
Hypothesis If: injective f.

Lemma exists_preim p x: [exists a in preim f (pred1 (f x)), p a] = p x.
Proof.
  apply/existsP/idP.
  - by move=> [a /andP [/eqP /If ->]].
  - move=> H. exists x. apply/andP; split=> //. by apply/eqP.
Qed.

Lemma fnrel_im_pre r: fnrelpre (fnrelim r) = r.
Proof.
  rewrite /fnrelpre /=. apply/fnrelP=> a b.
  do 2 rewrite fnrelE /=. rewrite 2!exists_preim //.
Qed.

End InjImage.

End Image.

