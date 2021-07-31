Require Import Basics.
Require Import Setoid.
Require Import RelationClasses.

Require Import Ensembles.
Require Import Constructive_sets.

From Practice Require Import Base.
From Practice Require Import Functions.

(* Uniqueness on Type gives rise to partial functions *)
Module Unique_Extras.

Definition sig_uniq {A:Type} (P: A -> Prop) := sig (unique P).

Notation "'uniq' x , p" := (sig_uniq (fun x => p))
  (at level 200, x binder, right associativity): type_scope.

Lemma sigma_to_unique (A: Type) (P: A -> Prop) :
  uniqueness P -> {x | P x} -> uniq x, P x.
Proof. intros H [x K]. exists x. split; auto. Qed.

Definition get {A:Type} {P: A -> Prop} (pf: sig P): A
  := proj1_sig pf.

Definition getPr {A:Type} {P: A -> Prop} (pf: sig P): P (get pf)
  := proj2_sig pf.

Property get_unique_spec (A: Type) (P: A -> Prop) (E: uniq x, P x): unique P (get E).
Proof. destruct E. auto. Qed.

#[export]
Hint Resolve sigma_to_unique get_unique_spec : core.

End Unique_Extras.

(* ----------------------------------------------------------------- *)
(* Extra Set theoretical logic to the barebone Ensembles *)
Module Set_Extras.
Import Function_Extras.
Include Unique_Extras.

Notation "x ':in:' A" := (In _ A x) (at level 70).
Notation "{|' x '|}" := (Singleton _ x) (at level 50).
Notation "A '//\\' B" := (Intersection _ A B) (at level 60).
Notation "A '\\//' B" := (Union _ A B) (at level 60).
Notation "'~!' A" := (Complement _ A) (at level 20).
Notation "A '\\' B" := (Setminus _ A B) (at level 65).

Notation "A '~~' B" := (Same_set _ A B) (at level 80).
Notation "A '<:=' B" := (Included _ A B) (at level 70).
Notation "A '=:>' B" := (Included _ B A) (at level 70).

Instance set_incl U: PreOrder (Included U).
Proof. split; auto with sets. Qed.

Instance set_equiv U: Equivalence (Same_set U).
Proof.
  split; auto with sets.
  - unfold Symmetric. unfold Same_set. tauto.
  - unfold Transitive. unfold Same_set. intros ? ? ? [] []. split; etransitivity; eauto.
Qed.

Add Parametric Relation U: (Ensemble U) (Same_set U)
  reflexivity proved by reflexivity
  symmetry proved by symmetry
  transitivity proved by transitivity
  as eq_set.

Lemma eq_set_prop: forall U (A B: Ensemble U),
  A ~~ B <-> (forall x, x :in: A <-> x :in: B).
Proof.
  split.
  - intros [HIF HOF]. unfold Included in *. split; auto.
  - intros H. split; unfold Included in *; apply H.
Qed.
Corollary eqset_is_exteq: forall U (A B: Ensemble U),
  A ~~ B <-> ext_eq iff A B.
Proof. intros. apply eq_set_prop. Qed.

Add Parametric Morphism U: (In U)
  with signature (Same_set U) ==> eq ==> iff as in_mor.
Proof. intros. rewrite eq_set_prop in H. unfold In in *. auto. Qed.

Add Parametric Morphism U: (Included U)
  with signature (Same_set U) ==> (Same_set U) ==> iff as inc_mor.
Proof. intros. unfold Included. rw_refl. Qed.


Property union_iff: forall U (B C: Ensemble U) x, x :in: B \\// C <-> x :in: B \/ x :in: C.
Proof. intros. split; [ apply Union_inv | intros [? | ?]; auto with sets ]. Qed.
Property intersection_iff: forall U (B C: Ensemble U) x, x :in: B //\\ C <-> x :in: B /\ x :in: C.
Proof. intros. split; [ apply Intersection_inv | intros [? ?]; auto with sets ]. Qed.

Add Parametric Morphism U: (Union U)
  with signature (Same_set U) ==> (Same_set U) ==> (Same_set U) as union_mor.
Proof. intros. apply eq_set_prop. setoid_rewrite union_iff. rw_refl. Qed.

Add Parametric Morphism U: (Intersection U)
  with signature (Same_set U) ==> (Same_set U) ==> (Same_set U) as inter_mor.
Proof. intros. apply eq_set_prop. setoid_rewrite intersection_iff. rw_refl. Qed.

Add Parametric Morphism U: (Complement U)
  with signature (Same_set U) ==> (Same_set U) as comp_mor.
Proof. intros. unfold Complement. rewrite eq_set_prop in *. unfold In in *. firstorder. Qed.

(* Properties of set operations *)

Section SetOps.
Context {U: Type}.

Property included_full: forall B: Ensemble U, B <:= Full_set U.
Proof. unfold Included. intros. constructor. Qed.

Property union_comm: forall B C: Ensemble U, B \\// C ~~ C \\// B.
Proof. setoid_rewrite eq_set_prop. setoid_rewrite union_iff. tauto. Qed.
Property union_assoc: forall A B C: Ensemble U, A \\// (B \\// C) ~~ (A \\// B) \\// C.
Proof. setoid_rewrite eq_set_prop. repeat setoid_rewrite union_iff. tauto. Qed.

Property intersection_comm: forall B C: Ensemble U, B //\\ C ~~ C //\\ B.
Proof. setoid_rewrite eq_set_prop. setoid_rewrite intersection_iff. tauto. Qed.
Property intersection_assoc: forall A B C: Ensemble U, A //\\ (B //\\ C) ~~ (A //\\ B) //\\ C.
Proof. setoid_rewrite eq_set_prop. repeat setoid_rewrite intersection_iff. tauto. Qed.

Property union_incl: forall B C: Ensemble U, B <:= B \\// C.
Proof. unfold Included. setoid_rewrite union_iff. tauto. Qed.
Property union_incl2: forall B C: Ensemble U, C <:= B \\// C.
Proof. unfold Included. setoid_rewrite union_iff. tauto. Qed.

Property intersection_incl: forall B C: Ensemble U, B //\\ C <:= B.
Proof. unfold Included. setoid_rewrite intersection_iff. tauto. Qed.
Property intersection_incl2: forall B C: Ensemble U, B //\\ C <:= C.
Proof. unfold Included. setoid_rewrite intersection_iff. tauto. Qed.

Property union_incl_split: forall A B C: Ensemble U, A \\// B <:= C <-> A <:= C /\ B <:= C.
Proof. unfold Included. setoid_rewrite union_iff. firstorder. Qed.

Property intersection_incl_split: forall A B C: Ensemble U, C <:= A //\\ B <-> C <:= A /\ C <:= B.
Proof. unfold Included. setoid_rewrite intersection_iff. firstorder. Qed.

Property included_union: forall B C: Ensemble U, B <:= C <-> B \\// C ~~ C.
Proof. unfold Included. setoid_rewrite eq_set_prop. setoid_rewrite union_iff. firstorder. Qed.

Property included_intersection: forall B C: Ensemble U, B <:= C <-> B //\\ C ~~ B.
Proof. unfold Included. setoid_rewrite eq_set_prop. setoid_rewrite intersection_iff. firstorder. Qed.

Lemma intersection_incl_distr: forall A B C D: Ensemble U,
  A <:= B -> C <:= D -> A //\\ C <:= B //\\ D.
Proof. intros. apply intersection_incl_split. split; etransitivity; eauto;
  [apply intersection_incl | apply intersection_incl2]. Qed.

Lemma union_incl_distr: forall A B C D: Ensemble U,
  A <:= B -> C <:= D -> A \\// C <:= B \\// D.
Proof. intros. apply union_incl_split. split; etransitivity; eauto;
  [apply union_incl | apply union_incl2]. Qed.

End SetOps.

(* Qualification over sets *)
Definition ExistsIn {U:Type} (A: Ensemble U) (P: U -> Prop) : Prop :=
  exists x: U, x :in: A /\ P x.
Definition ForallIn {U:Type} (A: Ensemble U) (P: U -> Prop) : Prop :=
  forall x: U, x :in: A -> P x.

Add Parametric Morphism U (A: Ensemble U): (ExistsIn A)
  with signature (gen_ext_eq A iff) ==> iff as exists_mor.
Proof. unfold ExistsIn. intros. split; intros [? []]; eexists; split; eauto; firstorder. Qed.

Add Parametric Morphism U (A: Ensemble U): (ForallIn A)
  with signature (gen_ext_eq A iff) ==> iff as forall_mor.
Proof. unfold ForallIn. intros. split; intros; specialize (H0 x0); firstorder. Qed.

(* Power set: Set of sets on U - Powerset is the proper version *)
Definition PowerEn (U:Type) := Ensemble (Ensemble U).

Definition properPset {U:Type} (P: PowerEn U): Prop := Morphisms.Proper (Same_set U ==> iff) P.
Definition Powerset (U:Type) := { P: PowerEn U | properPset P }.

Definition Same_pset (U:Type) := fun P Q: Powerset U => get P ~~ get Q.

Instance pset_equiv U: Equivalence (Same_pset U).
Proof. unfold Same_pset. split; auto with sets.
  - unfold Symmetric. symmetry; auto. - unfold Transitive. etransitivity; eauto. Qed.

Add Parametric Relation U: (Powerset U) (Same_pset U)
  reflexivity proved by reflexivity
  symmetry proved by symmetry
  transitivity proved by transitivity
  as eq_pset.
Add Parametric Morphism U: get
  with signature (Same_pset U) ==> (Same_set (Ensemble U)) as get_mor.
Proof. unfold Same_pset. trivial. Qed.

(* Powerset on certain set *)
Definition PSeton {U:Type} (A: Ensemble U): PowerEn U := fun V => V <:= A.

Add Parametric Morphism U: PSeton
  with signature (Same_set U) ==> (Same_set (Ensemble U)) as pseton_mor.
Proof. unfold PSeton. intros. apply eq_set_prop. unfold In. rw_refl. Qed.

Inductive Unions {U:Type} (F: PowerEn U): Ensemble U :=
  intro_unions: forall x, ExistsIn F (fun A => x :in: A) -> x :in: Unions F.
Inductive Intersects {U:Type} (F: PowerEn U): Ensemble U :=
  intro_intersects: forall x, ForallIn F (fun A => x :in: A) -> x :in: Intersects F.

Property unions_iff: forall U x (F: PowerEn U), x :in: Unions F <-> ExistsIn F (fun A => x :in: A).
Proof. split; [ intros [] | constructor ]; trivial. Qed.
Property intersects_iff: forall U x (F: PowerEn U), x :in: Intersects F <-> ForallIn F (fun A => x :in: A).
Proof. split; [ intros [] | constructor ]; trivial. Qed.

Add Parametric Morphism U: Unions
  with signature (Same_set (Ensemble U)) ==> (Same_set U) as unions_mor.
Proof. intros. apply eq_set_prop. setoid_rewrite unions_iff. unfold ExistsIn. rw_refl. Qed.
Add Parametric Morphism U: Intersects
  with signature (Same_set (Ensemble U)) ==> (Same_set U) as intersects_mor.
Proof. intros. apply eq_set_prop. setoid_rewrite intersects_iff. rw_refl. Qed.

Property unions_inc_one: forall U (A: Ensemble U) (F: PowerEn U),
  A :in: F -> A <:= Unions F.
Proof. intros. unfold Included. intros. apply unions_iff. exists A. auto. Qed.

Property intersects_inced_one: forall U (A: Ensemble U) (F: PowerEn U),
  A :in: F -> A =:> Intersects F.
Proof. intros. unfold Included. intros. apply intersects_iff in H0. firstorder. Qed.


Lemma unions_empty: forall X,
  Unions (Empty_set (Ensemble X)) ~~ Empty_set X.
Proof. setoid_rewrite eq_set_prop. intros. split; try contradiction.
  intros H. apply unions_iff in H as [? []]. contradiction. Qed.

Lemma intersects_empty: forall X,
  Intersects (Empty_set (Ensemble X)) ~~ Full_set X.
Proof. setoid_rewrite eq_set_prop. intros. split; constructor.
  intros ? ?. contradiction. Qed.


Lemma inc_forall_unions_iff: forall U (A: Ensemble U) (F: PowerEn U),
  ForallIn F (fun U => A =:> U) <-> A =:> Unions F.
Proof. intros. split; intros.
  - unfold Included. intros x Hx. apply unions_iff in Hx as [B []]. firstorder.
  - intros B HB. etransitivity; eauto. apply unions_inc_one. auto.
Qed.

Lemma inced_forall_intersects_iff: forall U (A: Ensemble U) (F: PowerEn U),
  ForallIn F (fun U => A <:= U) <-> A <:= Intersects F.
Proof. intros. split; intros.
  - unfold Included. intros x Hx. apply intersects_iff. firstorder.
  - intros B HB. etransitivity; eauto. apply intersects_inced_one. auto.
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
Hint Unfold ExistsIn ForallIn PowerEn properPset Powerset Same_pset
  UnionList IntersectList: sets.
#[export]
Hint Constructors Unions Intersects: sets.
#[export]
Hint Resolve included_full
  union_comm union_assoc intersection_comm intersection_assoc
  union_incl union_incl2 intersection_incl intersection_incl2
  union_incl_distr intersection_incl_distr
  unions_inc_one intersects_inced_one unions_empty intersects_empty: sets.
#[export]
Hint Resolve -> eq_set_prop eqset_is_exteq union_incl_split intersection_incl_split
  included_union included_intersection unions_iff intersects_iff: sets.
#[export]
Hint Resolve <- eq_set_prop eqset_is_exteq union_incl_split intersection_incl_split
  included_union included_intersection unions_iff intersects_iff: sets.

End Set_Extras.
