Require Import Basics.
Require Import Setoid.
Require Import RelationClasses.

Require Import Orders.
Require Import OrdersTac.

Require Import Ensembles.
Require Import Constructive_sets.

Module Type PartialOrder := StrOrder <+ HasLe <+ LeIsLtEq.

(* ----------------------------------------------------------------- *)
(* Set theoretical logic based on type T with usual equality *)
Module SetOn (Import E: UsualEqualityType).
Definition U : Type := t.

(* Setoid_rewrites all occurrences, until it meets True. Renames hypothesis. *)
Ltac all_rewrite := let BLOCK := True in
  let rec rec_rewrite :=
    lazymatch goal with
    | [ |- BLOCK -> _ ] => intros _
    | [ |- ?R ?x ?y -> _ ] =>
      let E := fresh "E" in intros E; try setoid_rewrite E; rec_rewrite
    end in
  generalize (I : BLOCK);
  repeat match goal with
  | [ E: ?R ?x ?y |- _ ] => revert E
  end; rec_rewrite.

(* Rewrites all occurrences to match for reflexivity. *)
Ltac rw_refl := all_rewrite; reflexivity.

Notation "x ':in:' A" := (In U A x) (at level 70).
Notation "A '//\\' B" := (Intersection U A B) (at level 60).
Notation "A '\\//' B" := (Union U A B) (at level 60).
Notation "A ~~ B" := (Same_set U A B) (at level 80).
Notation "A <:= B" := (Included U A B) (at level 70).
Notation "A =:> B" := (Included U B A) (at level 70).

Instance set_incl : PreOrder (Included U).
Proof. split; auto with sets. Qed.

Instance set_equiv : Equivalence (Same_set U).
Proof.
  split; auto with sets.
  - unfold Symmetric. unfold Same_set. tauto.
  - unfold Transitive. unfold Same_set. intros A B C. split; transitivity B; tauto.
Qed.

Add Parametric Relation : (Ensemble U) (Same_set U)
  reflexivity proved by (reflexivity (R := Same_set U))
  symmetry proved by (symmetry (R := Same_set U))
  transitivity proved by (transitivity (R := Same_set U))
  as eq_set.

Lemma eq_set_prop: forall (A B: Ensemble U),
  A ~~ B <-> (forall x, x :in: A <-> x :in: B).
Proof.
  split.
  - intros [HIF HOF]. unfold Included in *. split; auto.
  - intros H. split; unfold Included in *; apply H.
Qed.

Add Parametric Morphism : (In U)
  with signature (Same_set U) ==> Logic.eq ==> iff as in_mor.
Proof. intros. rewrite eq_set_prop in H. unfold In in *. auto. Qed.

Add Parametric Morphism : (Included U)
  with signature (Same_set U) ==> (Same_set U) ==> iff as inc_mor.
Proof. intros. unfold Included. rw_refl. Qed.

Property union_iff: forall (B C: Ensemble U) x, x :in: B \\// C <-> x :in: B \/ x :in: C.
Proof. intros. split; [ apply Union_inv | intros [? | ?]; auto with sets ]. Qed.
Add Parametric Morphism : (Union U)
  with signature (Same_set U) ==> (Same_set U) ==> (Same_set U) as inc_union.
Proof. intros. apply eq_set_prop. setoid_rewrite union_iff. rw_refl. Qed.

Property intersection_iff: forall (B C: Ensemble U) x, x :in: B //\\ C <-> x :in: B /\ x :in: C.
Proof. intros. split; [ apply Intersection_inv | intros [? ?]; auto with sets ]. Qed.
Add Parametric Morphism : (Intersection U)
  with signature (Same_set U) ==> (Same_set U) ==> (Same_set U) as inc_inter.
Proof. intros. apply eq_set_prop. setoid_rewrite intersection_iff. rw_refl. Qed.

Lemma included_intersection: forall B C: Ensemble U, B <:= C <-> B //\\ C ~~ B.
Proof. unfold Included. setoid_rewrite eq_set_prop. setoid_rewrite intersection_iff. firstorder. Qed.

Lemma included_union: forall B C: Ensemble U, B <:= C <-> B \\// C ~~ C.
Proof. unfold Included. setoid_rewrite eq_set_prop. setoid_rewrite union_iff. firstorder. Qed.

#[export]
Hint Resolve eq_set_prop : sets.
#[export]
Hint Resolve -> included_intersection included_union : sets.
#[export]
Hint Resolve <- included_intersection included_union : sets.

End SetOn.

(* ----------------------------------------------------------------- *)

Module InfSup (Import O: UsualTotalOrder').
Module S := SetOn O. Import S.
Module OF := OrderFacts O O. Import OF.
Module MOT := MakeOrderTac O O. Import MOT.

Inductive Direction : Type :=
  | LT | GT.
Definition dnot (d: Direction) : Direction :=
  match d with
  | LT => GT | GT => LT end.
Definition ord_dir (d: Direction) : U -> U -> Prop :=
  match d with
  | LT => le
  | GT => flip le
  end.
Definition ord_str_dir (d: Direction) : U -> U -> Prop :=
  match d with
  | LT => lt
  | GT => flip lt
  end.
Notation "x '[!' d '!]' y" := (ord_dir d x y) (at level 60).
Notation "x '<!' d '!>' y" := (ord_str_dir d x y) (at level 60).

Ltac order_dir d := destruct d; unfold ord_dir in *; unfold flip in *; order.

Property dord_ref: forall d a, a [!d!] a.
Proof. order_dir d. Qed.
Property dord_trans: forall d a b c, a [!d!] b -> b [!d!] c -> a [!d!] c.
Proof. order_dir d. Qed.
Property dord_antisym: forall d a b, a [!d!] b -> b [!d!] a -> a = b.
Proof. order_dir d. Qed.
Property dnot_sym: forall d a b, b [!dnot d!] a <-> a [!d!] b.
Proof. destruct d; unfold dnot; unfold ord_dir; tauto. Qed.

Instance PreOrder d: PreOrder (ord_dir d).
Proof. split.
  - unfold Reflexive. apply dord_ref.
  - unfold Transitive. apply dord_trans.
Qed.
(* Not proving partial order, too complex definition *)
Instance Antisymmetric d: Antisymmetric _ eq (ord_dir d).
Proof. unfold Antisymmetric. apply dord_antisym. Qed.

#[export]
Hint Constructors Direction: ordered_type.
#[export]
Hint Unfold dnot ord_dir ord_str_dir: ordered_type.
#[export]
Hint Resolve dord_ref dord_trans dord_antisym: ordered_type.
#[export]
Hint Resolve <- dnot_sym: ordered_type.
#[export]
Hint Resolve -> dnot_sym: ordered_type.

(* ----------------------------------------------------------------- *)

Section Directed.
Variable d: Direction.

Section Single_Ensemble.
Variable A: Ensemble U.

Definition Bound b : Prop := 
  forall x, x :in: A -> b [!d!] x.
Definition Extremum m : Prop :=
  m :in: A /\ Bound m.

Definition Bounded_D : Prop :=
  exists b, Bound b.
Definition Extr : Prop :=
  exists ! m, Extremum m.

End Single_Ensemble.

(* Encapsulation of Bound as a set(Ensemble) *)
Inductive Bnds (A: Ensemble U) : Ensemble U :=
  bnd_intro : forall b:U, Bound A b -> b :in: Bnds A.
Inductive Range_inc (a: U) : Ensemble U :=
  rn_inc_intro : forall x:U, (a [!d!] x) -> x :in: Range_inc a.
Inductive Range_exc (a: U) : Ensemble U :=
  rn_exc_intro : forall x:U, a <!d!> x -> x :in: Range_exc a.

Local Ltac single_constr_iff := intros; split; [ intros H; destruct H | constructor ]; auto.

(* Bnds properties *)
Property bnds_iff: forall A b, b :in: Bnds A <-> Bound A b.
Proof. single_constr_iff. Qed.

(* Range properties *)
Property range_inc_iff: forall a x, x :in: Range_inc a <-> a [!d!] x.
Proof. single_constr_iff. Qed.
Property range_exc_iff: forall a x, x :in: Range_exc a <-> a <!d!> x.
Proof. single_constr_iff. Qed.

Property range_incl: forall a, a :in: Range_inc a.
Proof. intros. apply range_inc_iff. order_dir d. Qed.
Property range_incl_extreme: forall a, Extremum (Range_inc a) a.
Proof.
  intros. unfold Extremum. split; try apply range_incl.
  unfold Bound. intros. destruct H. assumption.
Qed.
Property range_inc_include_iff: forall a b,
  a [!d!] b <-> Range_inc a =:> Range_inc b.
Proof. unfold Included. split; intros.
  - rewrite range_inc_iff in *. eauto with ordered_type.
  - specialize (H b). repeat rewrite range_inc_iff in H. auto with ordered_type.
Qed.

Property range_included: forall a b, a [!d!] b <-> Range_inc a =:> Range_inc b.
Proof. unfold Included. split; repeat setoid_rewrite range_inc_iff; eauto with ordered_type. Qed.

End Directed.

Definition Bounded A := Bounded_D LT A /\ Bounded_D GT A.

Definition Minimum := Extremum LT.
Definition Maximum := Extremum GT.

(* Supremum and Infimum *)
Definition Limfemum (d: Direction) (A: Ensemble U) (s: U) : Prop :=
  Extremum (dnot d) (Bnds d A) s.
Definition Infimum := Limfemum LT.
Definition Supremum := Limfemum GT.

Definition Limf (d: Direction) (A: Ensemble U) : Prop :=
  exists! s, Limfemum d A s.

Notation "[' a '|" := (Range_inc LT a).
Notation "|' a ']" := (Range_inc GT a).
Notation "(' a '|" := (Range_exc LT a).
Notation "|' a ')" := (Range_exc GT a).

Definition Interval (incl_a incl_b: bool) (a b: U) :=
  match incl_a, incl_b with
  | true, true => [' a '| \\// |' b ']
  | true, false => [' a '| \\// |' b ')
  | false, true => (' a '| \\// |' b ']
  | false, false => (' a '| \\// |' b ')
  end.

Notation "[' a , b ']" := (Interval true true a b).
Notation "[' a , b ')" := (Interval true false a b).
Notation "(' a , b ']" := (Interval false true a b).
Notation "(' a , b ')" := (Interval false false a b).

(* Hints and morphisms *)
#[export]
Hint Unfold Bound Extremum Bounded_D Extr Bounded Minimum Maximum
  Limfemum Supremum Infimum Interval: ordered_type.
#[export]
Hint Constructors Bnds Range_inc Range_exc: ordered_type.
#[export]
Hint Immediate range_incl: ordered_type.
#[export]
Hint Resolve -> range_inc_iff range_exc_iff range_inc_include_iff: ordered_type.
#[export]
Hint Resolve <- range_inc_iff range_exc_iff range_inc_include_iff: ordered_type.
#[export]
Hint Resolve range_incl_extreme: ordered_type.

Add Parametric Morphism : Bound
  with signature Logic.eq ==> (Same_set U) ==> Logic.eq ==> iff as bound_mor.
Proof. unfold Bound. intros. rw_refl. Qed.
Add Parametric Morphism : Extremum
  with signature Logic.eq ==> (Same_set U) ==> Logic.eq ==> iff as ext_mor.
Proof. unfold Extremum. intros. rw_refl. Qed.
Add Parametric Morphism : Bounded_D
  with signature Logic.eq ==> (Same_set U) ==> iff as bddd_mor.
Proof. unfold Bounded_D. intros. rw_refl. Qed.
Add Parametric Morphism : Extr
  with signature Logic.eq ==> (Same_set U) ==> iff as extr_mor.
Proof. unfold Extr. intros. unfold unique. rw_refl. Qed.

Add Parametric Morphism : Bnds (* The encapsulation requires further proof *)
  with signature Logic.eq ==> (Same_set U) ==> Same_set U as bnd_mor.
Proof.
  assert (bnds_same: forall d A, Bnds d A ~~ Bound d A). {
    setoid_rewrite eq_set_prop. apply bnds_iff. }
  setoid_rewrite bnds_same. intros. rewrite eq_set_prop. unfold In. rw_refl.
Qed.
Add Parametric Morphism : Bounded
  with signature (Same_set U) ==> iff as bdd_mor.
Proof. unfold Bounded. intros. rw_refl. Qed.
Add Parametric Morphism : Limfemum
  with signature Logic.eq ==> (Same_set U) ==> Logic.eq ==> iff as limf_mor.
Proof. unfold Limfemum. intros. rw_refl. Qed.
Add Parametric Morphism : Limf
  with signature Logic.eq ==> (Same_set U) ==> iff as limf'_mor.
Proof. unfold Limf. intros. unfold unique. rw_refl. Qed.

(* ----------------------------------------------------------------- *)

Lemma bound_equiv_in_range: forall d A b,
  Bound d A b <-> A <:= Range_inc d b.
Proof. unfold Bound. unfold Included. setoid_rewrite range_inc_iff. reflexivity. Qed.

Lemma bnds_contains_op_range: forall d A b,
  b :in: Bnds d A -> Bnds d A =:> Range_inc (dnot d) b.
Proof. unfold Included. intros.
  rewrite bnds_iff in *. rewrite bound_equiv_in_range in *. etransitivity; eauto with ordered_type. Qed.

Lemma bnds_included: forall d A B, A =:> B -> Bnds d A <:= Bnds d B.
Proof. unfold Included. intros. repeat rewrite bnds_iff in *. auto with ordered_type. Qed.

(* set union ~> bounds intersection *)
Lemma bnds_union: forall d A B, Bnds d (A \\// B) ~~ Bnds d A //\\ Bnds d B.
Proof. split.
- (* <:= *)
  unfold Included. intros. constructor; rewrite bnds_iff in *; unfold Bound in *; auto with sets.
- (* =:> *)
  unfold Included. intros. destruct H. rewrite bnds_iff in *. unfold Bound in *.
  intros y K. destruct K; auto.
Qed.

Property extremum_unique: forall d A, uniqueness (Extremum d A).
Proof.
  unfold uniqueness. unfold Extremum. intros ? ? ? ? [HI HB] [HI' HB'].
  assert (H: x [!d!] y /\ y [!d!] x). { split; auto with ordered_type. }
  eauto with ordered_type.
Qed.
Corollary ext_unique_find: forall d A s, Extremum d A s -> Extr d A.
Proof. intros. apply -> unique_existence. split. exists s. assumption. apply extremum_unique. Qed.

Corollary infsup_unique: forall d A, uniqueness (Limfemum d A).
Proof. unfold Limfemum. intros. apply extremum_unique. Qed.
Corollary infsup_unique_find: forall d A s, Limfemum d A s -> Limf d A.
Proof. intros. apply -> unique_existence. split. exists s. assumption. apply infsup_unique. Qed.

Lemma extremum_included: forall d A B m k,
  Extremum d A m -> Extremum d B k -> A =:> B -> m [!d!] k.
Proof. intros ? ? ? ? ? [AI AB] [BI BB] H. auto with ordered_type. Qed.

(* MAYBE implement forall_set and prove relevant properties *)
Lemma extremum_union: forall d A B m k,
  Extremum d A m -> Extremum d B k -> m [!d!] k -> Extremum d (A \\// B) m.
Proof. intros ? ? ? ? ? [AI AB] [BI BB] H. split; auto with sets.
  unfold Bound. intros ? K. destruct K; eauto with ordered_type.
Qed.

#[export]
Hint Resolve -> bound_equiv_in_range: ordered_type.
#[export]
Hint Resolve <- bound_equiv_in_range: ordered_type.
#[export]
Hint Resolve bnds_contains_op_range bnds_included
  extremum_unique infsup_unique extremum_included: ordered_type.


Property range_inc_bound: forall d a,
  Bnds d (Range_inc d a) ~~ Range_inc (dnot d) a.
Proof with (auto with ordered_type).
  intros. split... constructor. destruct H...
Qed.
Property range_inc_infsup: forall d a, Limfemum d (Range_inc d a) a.
Proof. intros. unfold Limfemum.
  setoid_rewrite range_inc_bound. apply range_incl_extreme. Qed.

(* Infimum/Supremum exists iff the bound is given as an inclusive range. *)
Lemma infsup_gives_bnds_range: forall d (A: Ensemble U) s,
  Limfemum d A s <-> Bnds d A ~~ Range_inc (dnot d) s.
Proof with (auto with ordered_type).
  unfold Limfemum. unfold Extremum. split.
  - (* -> *) intros [HI HB]. split...
  - (* <- *) intros H. setoid_rewrite H...
Qed.

Lemma infsup_included: forall d A B s t,
  Limfemum d A s -> Limfemum d B t -> A =:> B -> s [!d!] t.
Proof. intros ? ? ? ? ? HA HB H. rewrite infsup_gives_bnds_range in *. rewrite <- dnot_sym.
  eapply bnds_included in H. apply range_included. symmetry in HA. symmetry in HB. rw_refl.
Qed.

Lemma infsup_union: forall d A B s t,
  Limfemum d A s -> Limfemum d B t -> s [!d!] t -> Limfemum d (A \\// B) s.
Proof. intros ? ? ? ? ? HA HB H. rewrite infsup_gives_bnds_range in *. rewrite bnds_union.
  rewrite <- dnot_sym in H. apply range_included in H. all_rewrite. auto with sets.
Qed.

End InfSup.

