Require Import Basics.
Require Import Setoid.
Require Import RelationClasses.

Require Import Ensembles.
Require Import Constructive_sets.

From Practice Require Import Base.

(* ----------------------------------------------------------------- *)
(*        Extra Set theoretical logic to the barebone Ensembles      *)
(* ----------------------------------------------------------------- *)

Module Set_Extras.

Notation "x ':in:' A" := (In _ A x) (at level 70, no associativity).
Notation "{|' x '|}" := (Singleton _ x) (at level 50).
Notation "A '//\\' B" := (Intersection _ A B) (at level 60, right associativity).
Notation "A '\\//' B" := (Union _ A B) (at level 60, right associativity).
Notation "'~!' A" := (Complement _ A) (at level 20).
Notation "A '\\' B" := (Setminus _ A B) (at level 65, left associativity).

Notation "A '<:=' B" := (Included _ A B) (at level 70, no associativity).
Notation "A '=:>' B" := (Included _ B A) (at level 70, no associativity).

Instance set_incl U: PreOrder (Included U).
Proof. split; auto with sets. Qed.

Property same_set_eq: forall U (A B: Ensemble U),
  Same_set U A B <-> A '= B.
Proof. autounfold with sets. firstorder. Qed.

Program Instance setoid_set U: Setoid (Ensemble U) := {
  eqs := fun A B => forall x, x :in: A <-> x :in: B }.
Next Obligation.
  unfold In. split; red; [reflexivity | symmetry | etransitivity]; eauto.
Qed.

#[export]
Hint Unfold setoid_set: core.

Add Parametric Morphism U: (In U)
  with signature eqs ==> eq ==> iff as in_mor.
Proof. auto. Qed.

Add Parametric Morphism U: (Included U)
  with signature eqs ==> eqs ==> iff as inc_mor.
Proof. autounfold. firstorder. Qed.


Property union_iff: forall U (B C: Ensemble U) x,
  x :in: B \\// C <-> x :in: B \/ x :in: C.
Proof. intros. split;
  [ apply Union_inv | intros [? | ?]; auto with sets ]. Qed.

Property intersection_iff: forall U (B C: Ensemble U) x,
  x :in: B //\\ C <-> x :in: B /\ x :in: C.
Proof. intros. split;
  [ apply Intersection_inv | intros [? ?]; auto with sets ]. Qed.

Add Parametric Morphism U: (Union U)
  with signature eqs ==> eqs ==> eqs as union_mor.
Proof. autounfold. setoid_rewrite union_iff. firstorder. Qed.
Add Parametric Morphism U: (Intersection U)
  with signature eqs ==> eqs ==> eqs as inter_mor.
Proof. autounfold. setoid_rewrite intersection_iff. firstorder. Qed.

Add Parametric Morphism U: (Complement U)
  with signature eqs ==> eqs as comp_mor.
Proof. autounfold. unfold Complement. firstorder. Qed.

(* Properties of set operations *)

Section SetOps.
Context {U: Type}.

Property included_full: forall B: Ensemble U, B <:= Full_set U.
Proof. red. constructor. Qed.

Property union_comm: forall B C: Ensemble U, B \\// C '= C \\// B.
Proof. autounfold. setoid_rewrite union_iff. tauto. Qed.
Property union_assoc: forall A B C: Ensemble U, (A \\// B) \\// C '= A \\// (B \\// C).
Proof. autounfold. repeat setoid_rewrite union_iff. tauto. Qed.

Property intersection_comm: forall B C: Ensemble U, B //\\ C '= C //\\ B.
Proof. autounfold. setoid_rewrite intersection_iff. tauto. Qed.
Property intersection_assoc: forall A B C: Ensemble U, (A //\\ B) //\\ C '= A //\\ (B //\\ C).
Proof. autounfold. repeat setoid_rewrite intersection_iff. tauto. Qed.

Property union_incl: forall B C: Ensemble U, B <:= B \\// C.
Proof. red. setoid_rewrite union_iff. tauto. Qed.
Property union_incl2: forall B C: Ensemble U, C <:= B \\// C.
Proof. red. setoid_rewrite union_iff. tauto. Qed.

Property intersection_incl: forall B C: Ensemble U, B //\\ C <:= B.
Proof. red. setoid_rewrite intersection_iff. tauto. Qed.
Property intersection_incl2: forall B C: Ensemble U, B //\\ C <:= C.
Proof. red. setoid_rewrite intersection_iff. tauto. Qed.

Property union_incl_split: forall A B C: Ensemble U, A \\// B <:= C <-> A <:= C /\ B <:= C.
Proof. autounfold with sets. setoid_rewrite union_iff. firstorder. Qed.

Property intersection_incl_split: forall A B C: Ensemble U, C <:= A //\\ B <-> C <:= A /\ C <:= B.
Proof. autounfold with sets. setoid_rewrite intersection_iff. firstorder. Qed.

Property included_union: forall B C: Ensemble U, B <:= C <-> B \\// C '= C.
Proof. autounfold with core sets. setoid_rewrite union_iff. firstorder. Qed.

Property included_intersection: forall B C: Ensemble U, B <:= C <-> B //\\ C '= B.
Proof. autounfold with core sets. setoid_rewrite intersection_iff. firstorder. Qed.

Lemma intersection_incl_distr: forall A B C D: Ensemble U,
  A <:= B -> C <:= D -> A //\\ C <:= B //\\ D.
Proof. intros. apply intersection_incl_split.
  split; etransitivity; eauto; [apply intersection_incl | apply intersection_incl2]. Qed.

Lemma union_incl_distr: forall A B C D: Ensemble U,
  A <:= B -> C <:= D -> A \\// C <:= B \\// D.
Proof. intros. apply union_incl_split.
  split; etransitivity; eauto; [apply union_incl | apply union_incl2]. Qed.

End SetOps.

(* Qualification over sets *)
Definition ExistsIn {U:Type} (A: Ensemble U) (P: U -> Prop) : Prop :=
  exists x: U, x :in: A /\ P x.
Definition ForallIn {U:Type} (A: Ensemble U) (P: U -> Prop) : Prop :=
  forall x: U, x :in: A -> P x.

Add Parametric Morphism U (A: Ensemble U): (ExistsIn A)
  with signature (gen_ext_eq A eqs) ==> iff as exists_mor.
Proof. unfold ExistsIn. autounfold. firstorder. Qed.

Add Parametric Morphism U (A: Ensemble U): (ForallIn A)
  with signature (gen_ext_eq A eqs) ==> iff as forall_mor.
Proof. unfold ForallIn. autounfold. firstorder. Qed.

(* Power set: Set of sets on U - Powerset is the proper version *)
Definition PowerEn (U:Type) := Ensemble (Ensemble U).

Definition properPset {U:Type} (P: PowerEn U): Prop :=
  Morphisms.Proper (eqs ==> iff) P.
Definition Powerset (U:Type) := { P: PowerEn U | properPset P }.

(* Power set that is made proper *)
Definition properForm {U:Type} (P: PowerEn U): PowerEn U :=
  fun A => exists B, B :in: P /\ B '= A.
Property properForm_spec: forall U (P: PowerEn U), properPset (properForm P).
Proof. do 3 red. firstorder. Qed.

Definition asProper {U:Type} (P: PowerEn U): Powerset U :=
  exist _ _ (properForm_spec U P).


(* Powerset on certain set *)
Definition PSeton {U:Type} (A: Ensemble U): PowerEn U := fun V => V <:= A.

Add Parametric Morphism U: (@PSeton U)
  with signature eqs ==> eqs as pseton_mor.
Proof. unfold PSeton. autounfold. firstorder. Qed.

Inductive Unions {U:Type} (F: PowerEn U): Ensemble U :=
  intro_unions: forall x, ExistsIn F (fun A => x :in: A) -> x :in: Unions F.
Inductive Intersects {U:Type} (F: PowerEn U): Ensemble U :=
  intro_intersects: forall x, ForallIn F (fun A => x :in: A) -> x :in: Intersects F.

Property unions_iff: forall U x (F: PowerEn U),
  x :in: Unions F <-> ExistsIn F (fun A => x :in: A).
Proof. split; [ intros [] | constructor ]; trivial. Qed.
Property intersects_iff: forall U x (F: PowerEn U),
  x :in: Intersects F <-> ForallIn F (fun A => x :in: A).
Proof. split; [ intros [] | constructor ]; trivial. Qed.

Add Parametric Morphism U: (@Unions U)
  with signature eqs ==> eqs as unions_mor.
Proof. autounfold. setoid_rewrite unions_iff. firstorder. Qed.
Add Parametric Morphism U: (@Intersects U)
  with signature eqs ==> eqs as intersects_mor.
Proof. autounfold. setoid_rewrite intersects_iff. firstorder. Qed.

Property unions_inc_one: forall U (A: Ensemble U) (F: PowerEn U),
  A :in: F -> A <:= Unions F.
Proof. red. setoid_rewrite unions_iff. firstorder. Qed.

Property intersects_inced_one: forall U (A: Ensemble U) (F: PowerEn U),
  A :in: F -> A =:> Intersects F.
Proof. red. setoid_rewrite intersects_iff. firstorder. Qed.


Lemma unions_empty: forall X,
  Unions (Empty_set (Ensemble X)) '= Empty_set X.
Proof. autounfold. setoid_rewrite unions_iff. firstorder. Qed.

Lemma intersects_empty: forall X,
  Intersects (Empty_set (Ensemble X)) '= Full_set X.
Proof. autounfold. setoid_rewrite intersects_iff. firstorder. constructor. Qed.


Lemma inc_forall_unions_iff: forall U (A: Ensemble U) (F: PowerEn U),
  ForallIn F (fun U => A =:> U) <-> A =:> Unions F.
Proof. intros. split; intros.
  - red. intros x Hx. apply unions_iff in Hx as [B []]. firstorder.
  - intros B HB. etransitivity; eauto. apply unions_inc_one. auto.
Qed.

Lemma inced_forall_intersects_iff: forall U (A: Ensemble U) (F: PowerEn U),
  ForallIn F (fun U => A <:= U) <-> A <:= Intersects F.
Proof. intros. split; intros.
  - red. intros x Hx. apply intersects_iff. firstorder.
  - intros B HB. etransitivity; eauto. apply intersects_inced_one. auto.
Qed.

Lemma inced_forall_then_inced_unions: forall U (A: Ensemble U) (F: PowerEn U),
  Inhabited _ F -> ForallIn F (fun U => A <:= U) -> A <:= Unions F.
Proof.
  intros ? ? ? [B H1] H2. apply H2 in H1 as ?. etransitivity; eauto.
  apply unions_inc_one. assumption.
Qed.

Lemma inc_forall_then_inc_intersects: forall U (A: Ensemble U) (F: PowerEn U),
  Inhabited _ F -> ForallIn F (fun U => A =:> U) -> A =:> Intersects F.
Proof.
  intros ? ? ? [B H1] H2. apply H2 in H1 as ?. etransitivity; eauto.
  apply intersects_inced_one. assumption.
Qed.


(* Finite intersection/union via lists *)
Fixpoint UnionList {U:Type} (L: list (Ensemble U)): Ensemble U :=
  match L with
  | nil => Empty_set U
  | cons A L' => A \\// UnionList L'
  end.
Fixpoint IntersectList {U:Type} (L: list (Ensemble U)): Ensemble U :=
  match L with
  | nil => Full_set U
  | cons A L' => A //\\ IntersectList L'
  end.


#[export]
Hint Unfold ExistsIn ForallIn PowerEn properPset Powerset properForm PSeton
  UnionList IntersectList: sets.
#[export]
Hint Constructors Unions Intersects: sets.
#[export]
Hint Resolve included_full
  union_comm union_assoc intersection_comm intersection_assoc
  union_incl union_incl2 intersection_incl intersection_incl2
  union_incl_distr intersection_incl_distr      properForm_spec
  unions_inc_one intersects_inced_one unions_empty intersects_empty: sets.
#[export]
Hint Resolve -> same_set_eq union_incl_split intersection_incl_split
  included_union included_intersection unions_iff intersects_iff: sets.
#[export]
Hint Resolve <- same_set_eq union_incl_split intersection_incl_split
  included_union included_intersection unions_iff intersects_iff: sets.

End Set_Extras.
