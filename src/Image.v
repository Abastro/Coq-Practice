Require Import Basics.
Require Import Setoid.
Require Import RelationClasses.

Require Import Ensembles.
Require Import Constructive_sets.

From Practice Require Import Base.
From Practice Require Import Sets.

(* ----------------------------------------------------------------- *)
(*                    Image, Inverse Image(PreImage)                 *)
(* ----------------------------------------------------------------- *)

Module Images.
Import Set_Extras.

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

Property im_iff: forall (X: Ensemble U) (f: U -> V) (y: V),
  y :in: Im X f <-> exists x: U, (x :in: X) /\ f x = y.
Proof. split. apply im_inv. intros [x []]; subst. apply im_def. assumption. Qed.

Lemma im_empty: forall (f: U -> V),
  Im (Empty_set U) f '= Empty_set V.
Proof. autounfold. split; intros H; repeat destruct H. Qed.

Lemma im_intersect: forall (f: U -> V) (A B: Ensemble U),
  Im (A //\\ B) f <:= Im A f //\\ Im B f.
Proof. intros. autounfold with sets. intros y H.
  split; apply im_inv in H as [x []]; subst; destruct H; apply im_def; assumption. Qed.

Lemma im_union: forall (f: U -> V) (A B: Ensemble U),
  Im (A \\// B) f '= Im A f \\// Im B f.
Proof with (eauto using im_def with sets).
  intros; intros y. rewrite union_iff. repeat rewrite im_iff.
  setoid_rewrite union_iff. firstorder. Qed.

Lemma forall_im_iff: forall (P: Ensemble U) (f: U -> V) (g: V -> Prop),
  ForallIn (Im P f) g <-> ForallIn P (fun x => g (f x)).
Proof.
  intros. split.
  - intros H ? ?. apply H. apply im_def. assumption.
  - intros H ? [? []]%im_inv; subst. firstorder.
Qed.

Lemma exists_im_iff: forall (P: Ensemble U) (f: U -> V) (g: V -> Prop),
  ExistsIn (Im P f) g <-> ExistsIn P (fun x => g (f x)).
Proof.
  intros. split.
  - intros [? [[? []]%im_inv ?]]; subst. eauto with sets.
  - intros [? []]. eexists. split; eauto using im_def.
Qed.


Inductive InvIm (Y: Ensemble V) (f: U -> V): Ensemble U :=
  intro_invim: forall x: U, (f x) :in: Y -> x :in: InvIm Y f.

Property invim_iff: forall (Y: Ensemble V) (f: U -> V) (x: U),
  x :in: InvIm Y f <-> (f x) :in: Y.
Proof. split; intros; [destruct H | constructor]; auto. Qed.

Lemma invim_empty: forall (f: U -> V),
  InvIm (Empty_set V) f '= Empty_set U.
Proof. autounfold. split; intros H; repeat destruct H. Qed.

Lemma invim_full: forall (f: U -> V),
  InvIm (Full_set V) f '= Full_set U.
Proof. autounfold. split; intros H; repeat constructor. Qed.

Lemma invim_intersect: forall (f: U -> V) (A B: Ensemble V),
  InvIm (A //\\ B) f '= InvIm A f //\\ InvIm B f.
Proof. autounfold. setoid_rewrite intersection_iff. setoid_rewrite invim_iff.
  intros. apply intersection_iff. Qed.

Lemma invim_union: forall (f: U -> V) (A B: Ensemble V),
  InvIm (A \\// B) f '= InvIm A f \\// InvIm B f.
Proof. autounfold. setoid_rewrite union_iff. setoid_rewrite invim_iff.
  intros. apply union_iff. Qed.


Lemma invim_of_im_inc: forall (f: U -> V) (A: Ensemble U),
  InvIm (Im A f) f =:> A.
Proof. intros. intros x H. apply invim_iff. apply im_def. trivial. Qed.

Lemma inj_invim_of_im_eq: forall (f: U -> V) (A: Ensemble U),
  injective f -> InvIm (Im A f) f '= A.
Proof. intros. apply same_set_eq. split; [| apply invim_of_im_inc].
  intros x [x' [? E]] %invim_iff %im_inv. apply H in E; subst. trivial. Qed.

Lemma im_of_invim_inc: forall (f: U -> V) (B: Ensemble V),
  Im (InvIm B f) f <:= B.
Proof. intros. intros x [? []]%im_iff; subst. apply invim_iff. trivial. Qed.

Lemma surj_im_of_invim_eq: forall (f: U -> V) (B: Ensemble V),
  surjective f -> Im (InvIm B f) f '= B.
Proof. intros. apply same_set_eq. split; [apply im_of_invim_inc|].
  intros y ?. specialize (H y) as []; subst. apply im_def, invim_iff. trivial. Qed.

End Mapping.

Add Parametric Morphism U V `(UsualSetoid V): (@Im U V)
  with signature eqs ==> eqs ==> eqs as im_mor.
Proof. intros. intros s. repeat rewrite im_iff.
  split; intros [t []]; subst; autounfold in H1; exists t; firstorder. Qed.
Add Parametric Morphism U V: (@Im U V)
  with signature eqs ==> eq ==> eqs as im_eq_mor.
Proof. intros. intros s. repeat rewrite im_iff.
  split; intros [t []]; subst; firstorder. Qed.

Add Parametric Morphism U V `(UsualSetoid V): (@InvIm U V)
  with signature eqs ==> eqs ==> eqs as invim_mor.
Proof. intros. intros t. repeat rewrite invim_iff.
  specialize (H1 t). rw_refl. Qed.
Add Parametric Morphism U V: (@InvIm U V)
  with signature eqs ==> eq ==> eqs as invim_eq_mor.
Proof. intros. intros t. repeat rewrite invim_iff. auto. Qed.


Lemma im_identity: forall U (A: Ensemble U), Im A id '= A.
Proof. autounfold. intros. rewrite im_iff. firstorder. subst; auto. Qed.

Lemma invim_identity: forall U (A: Ensemble U), InvIm A id '= A.
Proof. autounfold. intros. setoid_rewrite invim_iff. reflexivity. Qed.


(* Image of Power set - used to denote indexed set *)
Section Mapping.
Context {U:Type} {V:Type}.

Inductive PowerIm (X: Ensemble U) (f: U -> Ensemble V): PowerEn V :=
  intro_powim: forall x: U, x :in: X -> forall A, A '= f x -> A :in: PowerIm X f.

Property powim_def: forall (X: Ensemble U) (f: U -> Ensemble V) x,
  x :in: X -> f x :in: PowerIm X f.
Proof. intros. econstructor; eauto. Qed.

Property powim_iff: forall (X: Ensemble U) (f: U -> Ensemble V) A,
  A :in: PowerIm X f <-> (exists x, x :in: X /\ A '= f x).
Proof. split; intros []; try (destruct H; econstructor); eauto. Qed.

End Mapping.

Add Parametric Morphism U V: (@PowerIm U V)
  with signature eqs ==> eqs ==> eqs as powim_mor.
Proof. intros. intros s. repeat rewrite powim_iff.
  split; intros [t []]; exists t; all_rewrite; eauto. Qed.

Notation "'indexed' i 'in' P , e" := (PowerIm P (fun i => e))
  (at level 90, i binder, right associativity).


#[export]
Hint Constructors Im InvIm PowerIm: sets.
#[export]
Hint Resolve im_def im_empty invim_empty invim_full
  invim_intersect invim_union im_identity invim_identity
  powim_def: sets.
#[export]
Hint Resolve -> im_iff invim_iff exists_im_iff forall_im_iff
  powim_iff: sets.
#[export]
Hint Resolve <- im_iff invim_iff exists_im_iff forall_im_iff
  powim_iff: sets.

(* ----------------------------------------------------------------- *)
(*                      UnionOver / IntersectOver                    *)
(* ----------------------------------------------------------------- *)

Definition UnionOver {U:Type} {V:Type} (P: Ensemble U) (f: U -> Ensemble V): Ensemble V :=
  Unions (PowerIm P f).
Definition IntersectOver {U:Type} {V:Type} (P: Ensemble U) (f: U -> Ensemble V): Ensemble V :=
  Intersects (PowerIm P f).

Notation "'unions' i 'in' P , e" := (UnionOver P (fun i => e))
  (at level 100, i binder, right associativity).
Notation "'intersects' i 'in' P , e" := (IntersectOver P (fun i => e))
  (at level 100, i binder, right associativity).

Property unionover_iff: forall U V (P: Ensemble U) (E: U -> Ensemble V) y,
  y :in: (unions x in P, E x) <-> ExistsIn P (fun x => y :in: E x).
Proof. intros. setoid_rewrite unions_iff. apply exists_im_iff. Qed.

Property intersectover_iff: forall U V (P: Ensemble U) (E: U -> Ensemble V) y,
  y :in: (intersects x in P, E x) <-> ForallIn P (fun x => y :in: E x).
Proof. intros. setoid_rewrite intersects_iff. apply forall_im_iff. Qed.

Add Parametric Morphism U V (P: U -> Prop): (@UnionOver U V P)
  with signature (gen_ext_eq P eqs) ==> eqs as unionover_mor.
Proof. autounfold. repeat setoid_rewrite unionover_iff. intros.
  apply exists_mor. autounfold. auto. Qed.

Add Parametric Morphism U V (P: U -> Prop): (@IntersectOver U V P)
  with signature (gen_ext_eq P eqs) ==> eqs as intersectover_mor.
Proof. autounfold. repeat setoid_rewrite intersectover_iff. intros.
  apply forall_mor. autounfold. auto. Qed.


Lemma unions_as_over: forall U (F: PowerEn U),
  (unions A in F, A) '= Unions F.
Proof. intros. unfold UnionOver. apply unions_mor. apply im_identity. Qed.

Lemma intersects_as_over: forall U (F: PowerEn U),
  (intersects A in F, A) '= Intersects F.
Proof. intros. unfold IntersectOver. apply intersects_mor. apply im_identity. Qed.


Lemma im_unionover: forall U V I (f: U -> V) (A: Ensemble I) (P: I -> Ensemble U),
  Im (unions i in A, P i) f '= unions i in A, Im (P i) f.
Proof with eauto with sets.
  intros. intros y. rewrite im_iff. setoid_rewrite unionover_iff. split.
  - intros [? [[? []] ?]]; subst...
  - intros [? [? [? []]%im_iff]]; subst. eexists...
Qed.

Lemma im_intersectover: forall U V I (f: U -> V) (A: Ensemble I) (P: I -> Ensemble U),
  Im (intersects i in A, P i) f <:= intersects i in A, Im (P i) f.
Proof.
  intros. intros y. rewrite im_iff. setoid_rewrite intersectover_iff.
  intros [? []]; subst. auto with sets. Qed.

Lemma unions_unionover: forall U I (A: Ensemble I) (F: I -> PowerEn U),
  Unions (unions i in A, F i) '= unions i in A, Unions (F i).
Proof with (eauto with sets).
  intros. intros x. split; intros H.
  - apply unions_iff in H as [V [H ?]]. apply unionover_iff in H as [i []].
    apply unionover_iff. eexists. rewrite unions_iff...
  - apply unionover_iff in H as [i [? H]]. apply unions_iff in H as [V []].
    apply unions_iff. eexists. rewrite unionover_iff...
Qed.
(* NOTE: Any inclusion for intersects & intersectover does not hold *)

Section OverOne.
Context (U:Type) (I:Type) (P: Ensemble I) (F: I -> Ensemble U).

Lemma inc_forall_unionover_iff: forall (A: Ensemble U),
  ForallIn P (fun i => A =:> F i) <-> A =:> unions i in P, F i.
Proof.
  etransitivity; [| eapply inc_forall_unions_iff].
  symmetry. etransitivity. eapply forall_im_iff. firstorder.
Qed.

Lemma inced_forall_intersecover_iff: forall (A: Ensemble U),
  ForallIn P (fun i => A <:= F i) <-> A <:= intersects i in P, F i.
Proof.
  etransitivity; [| eapply inced_forall_intersects_iff].
  symmetry. etransitivity. eapply forall_im_iff. firstorder.
Qed.

Lemma inced_forall_then_inced_unionover: forall (A: Ensemble U),
  Inhabited _ P -> ForallIn P (fun i => A <:= F i) -> A <:= unions i in P, F i.
Proof with (auto with sets).
  intros ? [] ?. apply inced_forall_then_inced_unions... exists (F x)...
Qed.

Lemma inc_forall_then_inc_intersectover: forall (A: Ensemble U),
  Inhabited _ P -> ForallIn P (fun i => A =:> F i) -> A =:> intersects i in P, F i.
Proof with (auto with sets).
  intros ? [] ?. apply inc_forall_then_inc_intersects... exists (F x)...
Qed.
End OverOne.


Local Lemma unions_exch_: forall U I J (A: Ensemble I) (B: Ensemble J)
  (R: I -> J -> Prop) (P: I -> J -> Ensemble U),
  (unions i in A, unions j in (B //\\ R i), P i j) <:=
  (unions j in B, unions i in (A //\\ flip R j), P i j).
Proof.
  intros. intros x H0.
  apply unionover_iff in H0 as [i [H1 H0]].
  apply unionover_iff in H0 as [j [H2 H0]].
  apply intersection_iff in H2 as [].
  apply unionover_iff. exists j. apply and_comm. split.
  apply unionover_iff. exists i. apply and_comm. split.
  assumption. split; auto. assumption.
Qed.
Lemma unions_exch: forall U I J (A: Ensemble I) (B: Ensemble J)
  (R: I -> J -> Prop) (P: I -> J -> Ensemble U),
  (unions i in A, unions j in (B //\\ R i), P i j) '=
  (unions j in B, unions i in (A //\\ flip R j), P i j).
Proof. split; apply unions_exch_. Qed.

Local Lemma intersects_exch_: forall U I J (A: Ensemble I) (B: Ensemble J)
  (R: I -> J -> Prop) (P: I -> J -> Ensemble U),
  (intersects i in A, intersects j in (B //\\ R i), P i j) <:=
  (intersects j in B, intersects i in (A //\\ flip R j), P i j).
Proof.
  intros. intros x H0.
  apply intersectover_iff; intros j H2.
  apply intersectover_iff; intros i H1.
  apply intersection_iff in H1 as [H1 ?].
  apply intersectover_iff in H0. specialize (H0 i H1). simpl in H0.
  apply intersectover_iff in H0. specialize (H0 j). apply H0.
  split; assumption.
Qed.
Lemma intersects_exch: forall U I J (A: Ensemble I) (B: Ensemble J)
  (R: I -> J -> Prop) (P: I -> J -> Ensemble U),
  (intersects i in A, intersects j in (B //\\ R i), P i j) '=
  (intersects j in B, intersects i in (A //\\ flip R j), P i j).
Proof. split; apply intersects_exch_. Qed.


Lemma invim_unionover: forall I U V (A: Ensemble I) (P: I -> Ensemble V) (f: U -> V),
  InvIm (unions i in A, P i) f '= unions i in A, InvIm (P i) f.
Proof.
  intros. autounfold. intros.
  rewrite invim_iff. repeat rewrite unionover_iff. apply exists_mor.
  red. intros i Ai. rewrite invim_iff. reflexivity.
Qed.

Lemma invim_intersectover: forall I U V (A: Ensemble I) (P: I -> Ensemble V) (f: U -> V),
  InvIm (intersects i in A, P i) f '= intersects i in A, InvIm (P i) f.
Proof.
  intros. autounfold. intros.
  rewrite invim_iff. repeat rewrite intersectover_iff. apply forall_mor.
  red. intros i Ai. rewrite invim_iff. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(*                              Subsets                              *)
(* ----------------------------------------------------------------- *)

Definition Subset {U:Type} (A: Ensemble U): Type := { x: U | A x }.

Section Subset.
Context {U:Type} {A: Ensemble U}.

(* inclusion *)
Definition incl: Subset A -> U := get.

(* Needs this form due to the problems of subset setoid *)
Lemma incl_im_of_invim: forall B, Im (InvIm B incl) incl '= A //\\ B.
Proof. intros. intros x. rewrite im_iff. rewrite intersection_iff. split.
  - intros [y []]; subst. split; [| apply invim_iff; trivial]. apply (getPr y).
  - intros [HI ?]. set (y := exist _ x HI). exists y. split; auto with sets.
Qed.

(* The lemma below requires proper set C over the setoid U. *)
(* Lemma incl_invim_of_im: forall C, InvIm (Im C incl) incl '= C.
Proof. intros. intros x. rewrite invim_iff. split; auto with sets.
  intros [x' []]%im_inv. *)

End Subset.

#[export]
Hint Unfold UnionOver IntersectOver Subset incl: sets.
#[export]
Hint Resolve unions_exch intersects_exch invim_unionover invim_intersectover
  incl_im_of_invim: sets.
#[export]
Hint Resolve -> unionover_iff intersectover_iff: sets.
#[export]
Hint Resolve <- unionover_iff intersectover_iff: sets.

End Images.
