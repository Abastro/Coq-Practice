Require Import Basics.
Require Import Setoid.
Require Import RelationClasses.

Require Import Ensembles.
Require Import Constructive_sets.

From Practice Require Import Old.Base.
From Practice Require Import Old.Sets.
From Practice Require Import Old.Image.

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


(* Sufficient condition of product inclusion *)
Lemma prod_incl_suff: forall (A C: Ensemble U) (B D: Ensemble V),
  A <:= C -> B <:= D -> A ** B <:= C ** D.
Proof. intros * H1 H2. intros (x, y) (Hx & Hy)%prod_iff. apply prod_iff. auto with sets. Qed.


Lemma im_fst_prod: forall (A: Ensemble U) (B: Ensemble V),
  Inhabited _ B -> Im (A ** B) fst '= A.
Proof. intros ? ? [y ?]. intros x. split.
  - intros [[u v] [[]%prod_iff ?]] %im_iff; subst. auto.
  - intros. econstructor; [ apply prod_iff; split; eauto | auto ].
Qed.

Lemma im_snd_prod: forall (A: Ensemble U) (B: Ensemble V),
  Inhabited _ A -> Im (A ** B) snd '= B.
Proof. intros ? ? [x ?]. intros y. split.
  - intros [[u v] [[]%prod_iff ?]] %im_iff; subst. auto.
  - intros. econstructor; [ apply prod_iff; split; eauto | auto ].
Qed.

Lemma invim_fst_prod: forall (A: Ensemble U), InvIm A fst '= A ** Full_set V.
Proof. intros ? (x,y). rewrite invim_iff. rewrite prod_iff. firstorder. constructor. Qed.

Lemma invim_snd_prod: forall (B: Ensemble V), InvIm B snd '= Full_set U ** B.
Proof. intros ? (x,y). rewrite invim_iff. rewrite prod_iff. firstorder. constructor. Qed.

Lemma prod_invim_split: forall (A: Ensemble U) (B: Ensemble V),
  InvIm A fst //\\ InvIm B snd '= A ** B.
Proof. intros * (x,y). rewrite intersection_iff, prod_iff, invim_iff, invim_iff. firstorder. Qed.

Lemma prod_intersect_exch: forall (A C: Ensemble U) (B D: Ensemble V),
  (A ** B) //\\ (C ** D) '= (A //\\ C) ** (B //\\ D).
Proof. intros. intros (x, y).
  rewrite intersection_iff. repeat rewrite prod_iff.
  repeat rewrite intersection_iff. tauto. Qed.

(* Subset and Product *)
Program Definition ps_to_sp {A: Ensemble U} {B: Ensemble V}:
  Subset A * Subset B -> Subset (A ** B) :=
  fun p => let (x, y) := p in exist _ (get x, get y) _.
Next Obligation. apply prod_iff. split. apply (getPr x). apply (getPr y). Qed.

Program Definition sp_to_ps {A: Ensemble U} {B: Ensemble V}:
  Subset (A ** B) -> Subset A * Subset B :=
  fun p => (exist _ (fst (get p)) _, exist _ (snd (get p)) _).
Next Obligation. assert (P := getPr p). destruct (get p). apply prod_iff in P. firstorder. Qed.
Next Obligation. assert (P := getPr p). destruct (get p). apply prod_iff in P. firstorder. Qed.

Property prod_sub_id: forall A B (x: Subset A) (y: Subset B),
  let (x', y') := sp_to_ps (ps_to_sp (x, y)) in get x' = get x /\ get y' = get y.
Proof. intros. simpl. intuition. Qed.

Property sub_prod_id: forall A B (t: Subset (A ** B)),
  get (ps_to_sp (sp_to_ps t)) = get t.
Proof. intros. destruct t as [(x, y) ?]. simpl. reflexivity. Qed.

End AProd.

#[export]
Hint Unfold ps_to_sp sp_to_ps: sets.
#[export]
Hint Constructors Product: sets.
#[export]
Hint Resolve empty_l_prod empty_r_prod full_prod  prod_incl_suff
  im_fst_prod im_snd_prod invim_fst_prod invim_snd_prod  prod_invim_split
  prod_intersect_exch: sets.
#[export]
Hint Resolve -> prod_iff: sets.
#[export]
Hint Resolve <- prod_iff: sets.

End Products.
