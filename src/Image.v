Require Import Basics.
Require Import Setoid.
Require Import RelationClasses.

Require Import Ensembles.
Require Import Constructive_sets.

From Practice Require Import Base.
From Practice Require Import Functions.
From Practice Require Import Sets.

Module Images.
Import Function_Extras.
Import Set_Extras.

(* Indexed not so useful rn, perhaps dedicate it to family? *)
(* Indexed set and Image, Inverse Image *)
Inductive Indexed {I:Type} {U:Type} (n: I -> U): Ensemble U :=
  intro_index: forall (i: I) (y: U), y = n i -> y :in: Indexed n.

Property index_def: forall I U (n: I -> U) (i: I),
  (n i) :in: Indexed n.
Proof. intros. econstructor; eauto. Qed.

Property index_inv: forall I U (n: I -> U) (y: U),
  y :in: Indexed n -> exists i: I, n i = y.
Proof. intros. destruct H. eauto. Qed.

Notation "{' i , e '}" := (Indexed (fun i => e)) (at level 60, i binder).

Add Parametric Morphism I U: (@Indexed I U)
  with signature def_ext_eq ==> (Same_set U) as ind_mor.
Proof. setoid_rewrite eq_set_prop.
  split; intros; apply index_inv in H0 as [i ?]; econstructor; subst; eauto. Qed.


Section Mapping.
Context {U:Type} {V:Type}.

Inductive Im (X: Ensemble U) (f: U -> V): Ensemble V :=
  intro_im: forall x: U, x :in: X -> forall y: V, y = f x -> y :in: Im X f.

Property im_def: forall (X: Ensemble U) (f: U -> V) (x: U),
  x :in: X -> f x :in: Im X f.
Proof. intros. econstructor; eauto. Qed.

Property im_inv: forall (X: Ensemble U) (f: U -> V) (y: V),
    y :in: Im X f -> exists x: U, (x :in: X) /\ f x = y.
Proof. intros. destruct H. eauto. Qed.

Lemma im_empty: forall (f: U -> V),
  Im (Empty_set U) f ~~ Empty_set V.
Proof. setoid_rewrite eq_set_prop. split; intros H; repeat destruct H. Qed.

Lemma im_full_is_index: forall (f: U -> V),
  Im (Full_set U) f ~~ Indexed f.
Proof. setoid_rewrite eq_set_prop. split; intros []; repeat econstructor; eauto. Qed.

Lemma im_intersect: forall (f: U -> V) (A B: Ensemble U),
  Im (A //\\ B) f <:= Im A f //\\ Im B f.
Proof. intros. unfold Included. intros y H.
  split; apply im_inv in H as [x []]; subst; destruct H; apply im_def; assumption. Qed.

Lemma im_union: forall (f: U -> V) (A B: Ensemble U),
  Im (A \\// B) f ~~ Im A f \\// Im B f.
Proof with (eauto using im_def with sets).
  intros. rewrite eq_set_prop. intros y. split; intros.
  - apply im_inv in H as [x []]; subst. rewrite union_iff in *. destruct H...
  - apply union_iff in H as [|]; apply im_inv in H as [? []]; subst; econstructor...
Qed.


Inductive InvIm (Y: Ensemble V) (f: U -> V): Ensemble U :=
  intro_invim: forall x: U, (f x) :in: Y -> x :in: InvIm Y f.

Property invim_iff: forall (Y: Ensemble V) (f: U -> V) (x: U),
  x :in: InvIm Y f <-> (f x) :in: Y.
Proof. split; intros; [destruct H | constructor]; auto. Qed.

Lemma invim_empty: forall (f: U -> V),
  InvIm (Empty_set V) f ~~ Empty_set U.
Proof. setoid_rewrite eq_set_prop. split; intros H; repeat destruct H. Qed.

Lemma invim_full: forall (f: U -> V),
  InvIm (Full_set V) f ~~ Full_set U.
Proof. setoid_rewrite eq_set_prop. split; intros H; repeat constructor. Qed.

Lemma invim_intersect: forall (f: U -> V) (A B: Ensemble V),
  InvIm (A //\\ B) f ~~ InvIm A f //\\ InvIm B f.
Proof. setoid_rewrite eq_set_prop.
  split; setoid_rewrite intersection_iff; repeat rewrite invim_iff; apply intersection_iff. Qed.

Lemma invim_union: forall (f: U -> V) (A B: Ensemble V),
  InvIm (A \\// B) f ~~ InvIm A f \\// InvIm B f.
Proof. setoid_rewrite eq_set_prop.
  split; setoid_rewrite union_iff; repeat rewrite invim_iff; apply union_iff. Qed.

End Mapping.

Add Parametric Morphism U V: Im
  with signature (Same_set U) ==> def_ext_eq ==> (Same_set V) as im_mor.
Proof. intros. setoid_rewrite eq_set_prop.
  split; intros; apply im_inv in H1 as [? []]; econstructor; try rewrite H in *; eauto; subst;
  [ | symmetry ]; apply H0. Qed.

Add Parametric Morphism U V: InvIm
  with signature (Same_set V) ==> (def_ext_eq) ==> (Same_set U) as invim_mor.
Proof. intros. setoid_rewrite eq_set_prop. intros. setoid_rewrite invim_iff.
  specialize (H0 x1). rw_refl. Qed.


Lemma im_identity: forall U (A: Ensemble U), Im A id ~~ A.
Proof. intros. apply eq_set_prop. split; intros H;
  [ apply im_inv in H as [? []]; subst; auto | econstructor; eauto]. Qed.

Lemma invim_identity: forall U (A: Ensemble U), InvIm A id ~~ A.
Proof. intros. apply eq_set_prop. intros. rewrite invim_iff. reflexivity. Qed.


Definition UnionOver {U:Type} {V:Type} (P: Ensemble U) (f: U -> Ensemble V): Ensemble V :=
  Unions (Im P f).
Definition IntersectOver {U:Type} {V:Type} (P: Ensemble U) (f: U -> Ensemble V): Ensemble V :=
  Intersects (Im P f).

Notation "'unions' i 'in' P , e" := (UnionOver P (fun i => e))
  (at level 100, i binder, right associativity).
Notation "'intersects' i 'in' P , e" := (IntersectOver P (fun i => e))
  (at level 100, i binder, right associativity).

Property unionover_iff: forall U V (P: Ensemble U) (E: U -> Ensemble V) y,
  y :in: (unions x in P, E x) <-> ExistsIn P (fun x => y :in: E x).
Proof. split; intros H.
  - apply unions_iff in H as [I [H ?]]. apply im_inv in H as [x []]; subst. eexists. eauto.
  - apply unions_iff. destruct H as [x []]. eexists. split; eauto. apply im_def. auto.
Qed.

Property intersectover_iff: forall U V (P: Ensemble U) (E: U -> Ensemble V) y,
  y :in: (intersects x in P, E x) <-> ForallIn P (fun x => y :in: E x).
Proof. split; intros H.
  - apply intersects_iff in H. intros x ?. specialize (H (E x)). apply H. apply im_def. auto.
  - apply intersects_iff. intros I H1. apply im_inv in H1 as [? []]; subst. auto.
Qed.

Add Parametric Morphism U V (P: U -> Prop): (UnionOver P)
  with signature gen_ext_eq P (Same_set V) ==> (Same_set V) as unionover_mor.
Proof. intros. apply eq_set_prop. intros ?. repeat rewrite unionover_iff.
  apply exists_mor. auto with sets. Qed.

Add Parametric Morphism U V (P: U -> Prop): (IntersectOver P)
  with signature gen_ext_eq P (Same_set V) ==> (Same_set V) as intersectover_mor.
Proof. intros. apply eq_set_prop. intros ?. repeat rewrite intersectover_iff.
  apply forall_mor. auto with sets. Qed.


Lemma unions_as_over: forall U (F: PowerEn U),
  (unions A in F, A) ~~ Unions F.
Proof. intros. unfold UnionOver. apply unions_mor. apply im_identity. Qed.

Lemma intersects_as_over: forall U (F: PowerEn U),
  (intersects A in F, A) ~~ Intersects F.
Proof. intros. unfold IntersectOver. apply intersects_mor. apply im_identity. Qed.


Lemma im_unionover: forall U V I (f: U -> V) (A: Ensemble I) (P: I -> Ensemble U),
  Im (unions i in A, P i) f ~~ unions i in A, Im (P i) f.
Proof.
  intros. apply eq_set_prop. intros y. rewrite unionover_iff. split; intros H.
  - apply im_inv in H as [x []]; subst. apply unionover_iff in H as [i []].
    exists i. auto using im_def.
  - destruct H as [i [? H]]. apply im_inv in H as [x []]; subst. apply im_def, unionover_iff.
    exists i. auto.
Qed.

Lemma im_intersectover: forall U V I (f: U -> V) (A: Ensemble I) (P: I -> Ensemble U),
  Im (intersects i in A, P i) f <:= intersects i in A, Im (P i) f.
Proof.
  intros. unfold Included. intros y. rewrite intersectover_iff. intros H.
  intros i HI. apply im_inv in H as [x []]; subst. apply im_def.
  apply intersectover_iff in H. auto.
Qed.

Lemma unions_unionover: forall U I (A: Ensemble I) (F: I -> PowerEn U),
  Unions (unions i in A, F i) ~~ unions i in A, Unions (F i).
Proof.
  intros. apply eq_set_prop. split; intros H.
  - apply unions_iff in H as [V [H ?]]. apply unionover_iff in H as [i []].
    apply unionover_iff. eexists. rewrite unions_iff. eauto with sets.
  - apply unionover_iff in H as [i [? H]]. apply unions_iff in H as [V []].
    apply unions_iff. eexists. rewrite unionover_iff. eauto with sets.
Qed.
(* NOTE: Any inclusion for intersects & intersectover does not hold *)

Local Lemma unions_exch_: forall U I J (A: Ensemble I) (B: Ensemble J)
  (R: I -> J -> Prop) (P: I -> J -> Ensemble U),
  (unions i in A, unions j in (B //\\ R i), P i j) <:=
  (unions j in B, unions i in (A //\\ flip R j), P i j).
Proof.
  intros. unfold Included. intros x H0.
  rewrite unionover_iff in H0. destruct H0 as [i [H1 H0]].
  rewrite unionover_iff in H0. destruct H0 as [j [H2 H0]].
  apply intersection_iff in H2 as [].
  rewrite unionover_iff. exists j. apply and_comm. split.
  rewrite unionover_iff. exists i. apply and_comm. split.
  assumption. split; auto. assumption.
Qed.
Lemma unions_exch: forall U I J (A: Ensemble I) (B: Ensemble J)
  (R: I -> J -> Prop) (P: I -> J -> Ensemble U),
  (unions i in A, unions j in (B //\\ R i), P i j) ~~
  (unions j in B, unions i in (A //\\ flip R j), P i j).
Proof. split; apply unions_exch_. Qed.

Local Lemma intersects_exch_: forall U I J (A: Ensemble I) (B: Ensemble J)
  (R: I -> J -> Prop) (P: I -> J -> Ensemble U),
  (intersects i in A, intersects j in (B //\\ R i), P i j) <:=
  (intersects j in B, intersects i in (A //\\ flip R j), P i j).
Proof.
  intros. unfold Included. intros x H0.
  rewrite intersectover_iff. intros j H2.
  rewrite intersectover_iff. intros i H1.
  apply intersection_iff in H1 as [H1 ?].
  rewrite intersectover_iff in H0. specialize (H0 i H1). simpl in H0.
  rewrite intersectover_iff in H0. specialize (H0 j). apply H0.
  split; assumption.
Qed.
Lemma intersects_exch: forall U I J (A: Ensemble I) (B: Ensemble J)
  (R: I -> J -> Prop) (P: I -> J -> Ensemble U),
  (intersects i in A, intersects j in (B //\\ R i), P i j) ~~
  (intersects j in B, intersects i in (A //\\ flip R j), P i j).
Proof. split; apply intersects_exch_. Qed.


Lemma invim_unionover: forall I U V (A: Ensemble I) (P: I -> Ensemble V) (f: U -> V),
  InvIm (unions i in A, P i) f ~~ unions i in A, InvIm (P i) f.
Proof.
  intros. apply eq_set_prop. intros.
  rewrite invim_iff. repeat rewrite unionover_iff. apply exists_mor.
  unfold gen_ext_eq. intros i Ai. rewrite invim_iff. reflexivity.
Qed.

Lemma invim_intersectover: forall I U V (A: Ensemble I) (P: I -> Ensemble V) (f: U -> V),
  InvIm (intersects i in A, P i) f ~~ intersects i in A, InvIm (P i) f.
Proof.
  intros. apply eq_set_prop. intros.
  rewrite invim_iff. repeat rewrite intersectover_iff. apply forall_mor.
  unfold gen_ext_eq. intros i Ai. rewrite invim_iff. reflexivity.
Qed.


#[export]
Hint Unfold UnionOver IntersectOver: sets.
#[export]
Hint Constructors Indexed Im InvIm: sets.
#[export]
Hint Resolve index_def index_inv im_def im_inv im_empty im_full_is_index
  invim_empty invim_full invim_intersect invim_union  im_identity invim_identity
  unions_exch intersects_exch
  invim_unionover invim_intersectover: sets.
#[export]
Hint Resolve -> invim_iff unionover_iff intersectover_iff: sets.
#[export]
Hint Resolve <- invim_iff unionover_iff intersectover_iff: sets.

End Images.
