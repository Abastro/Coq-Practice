Require Import Basics.
Require Import Setoid.
Require Import RelationClasses.

Require Import Ensembles.
Require Import Constructive_sets.

From Practice Require Import Base.
From Practice Require Import Sets.
From Practice Require Import Image.

(* Cartesian Product *)
Module Products.
Import Set_Extras.
Import Images.

Reserved Notation "A '**' B" (at level 40, left associativity).

Section AProd.
Context {U:Type} {V:Type}.

Inductive Product (A: Ensemble U) (B: Ensemble V): Ensemble (U * V) :=
  intro_prod: forall x y, x :in: A -> y :in: B -> (x, y) :in: A ** B
where "A '**' B" := (Product A B).

Property prod_iff: forall x y A B, (x, y) :in: A ** B <-> x :in: A /\ y :in: B.
Proof. intros. split; intros H; [ inversion H; subst; auto | constructor; tauto ]. Qed.

End AProd.

Notation "A '**' B" := (Product A B).

Add Parametric Morphism U V: (@Product U V)
  with signature eqs ==> eqs ==> eqs as prod_mor.
Proof. intros. intros []. repeat rewrite prod_iff. firstorder. Qed.

Section AProd.
Context {U:Type} {V:Type}.

Lemma empty_l_prod: forall B, Empty_set U ** B '= Empty_set (U * V).
Proof. autounfold. intros ? []. rewrite prod_iff. firstorder. Qed.
Lemma empty_r_prod: forall A, A ** Empty_set V '= Empty_set (U * V).
Proof. autounfold. intros ? []. rewrite prod_iff. firstorder. Qed.

Lemma full_prod: Full_set U ** Full_set V '= Full_set (U * V).
Proof. intros []. rewrite prod_iff. split; repeat constructor. Qed.


Lemma im_fst_prod: forall (A: Ensemble U) (B: Ensemble V),
  Inhabited _ B -> Im (A ** B) fst '= A.
Proof. intros ? ? [y ?]. intros x. split.
  - intros [[u v] [[]%prod_iff ?]] %im_inv; subst. auto.
  - intros. econstructor; [ apply prod_iff; split; eauto | auto ].
Qed.

Lemma im_snd_prod: forall (A: Ensemble U) (B: Ensemble V),
  Inhabited _ A -> Im (A ** B) snd '= B.
Proof. intros ? ? [x ?]. intros y. split.
  - intros [[u v] [[]%prod_iff ?]] %im_inv; subst. auto.
  - intros. econstructor; [ apply prod_iff; split; eauto | auto ].
Qed.

Lemma invim_fst_prod: forall (A: Ensemble U), InvIm A fst '= A ** Full_set V.
Proof. intros ? (x,y). rewrite invim_iff. rewrite prod_iff. firstorder. constructor. Qed.

Lemma invim_snd_prod: forall (B: Ensemble V), InvIm B snd '= Full_set U ** B.
Proof. intros ? (x,y). rewrite invim_iff. rewrite prod_iff. firstorder. constructor. Qed.

End AProd.

End Products.
