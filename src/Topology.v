Require Import Basics.
Require Import Setoid.
Require Import RelationClasses.

Require Import Ensembles.
Require Import Constructive_sets.

Require Import Fin.
Require List.

From Practice Require Import Base.
From Practice Require Import Sets.
From Practice Require Import Image.
From Practice Require Import Product.

Definition Fin := Fin.t.

Module ToposSet.
Import Base.
Import Set_Extras.
Import Images.
Import Products.

Record isTopology {X:Type} (open: Ensemble X -> Prop): Prop := {
  open_empty_total: open (Empty_set _) /\ open (Full_set _)
; open_union: forall (M: PowerEn X), ForallIn M open -> open (Unions M)
; open_intersect: forall U V: Ensemble X, open U -> open V -> open (U //\\ V)
}.
Definition Topology (X:Type) := { op: Powerset X | isTopology (get op) }.
Arguments open_empty_total {X} {open}.
Arguments open_union {X} {open}.
Arguments open_intersect {X} {open}.

Definition open {X:Type} (T: Topology X): Ensemble X -> Prop := get (get T).
(* Closed <-> complement is open *)
Definition closed {X:Type} (T: Topology X): Ensemble X -> Prop :=
  fun E => open(T) (~! E).

Definition covers {X:Type} (V: Ensemble X) (C: PowerEn X): Prop :=
  V <:= Unions C.
Notation cover_all := (covers (Full_set _)).

(* ----------------------------------------------------------------- *)
(*                         Topology Basis                            *)
(* ----------------------------------------------------------------- *)

Definition gopen {X:Type} {P: Powerset X -> Prop} (G: sig P): Ensemble X -> Prop := get (get G).

Record isBase {X:Type} (open: Ensemble X -> Prop) : Type := {
  bopen_cover: exists (C: PowerEn X), ForallIn C open /\ cover_all C
; bopen_intersect: forall (U V: Ensemble X) x,
  open U -> open V -> x :in: U //\\ V -> exists W, open W /\ x :in: W /\ (W <:= U //\\ V)
}.
Definition Basis (X:Type) := { op: Powerset X | isBase (get op) }.
Arguments bopen_cover {X} {open}.
Arguments bopen_intersect {X} {open}.

Record isSubbase {X:Type} (open: Ensemble X -> Prop) : Type := {
  sopen_cover: exists (C: PowerEn X), ForallIn C open /\ cover_all C
}.
Definition Subbasis (X:Type) := { op: Powerset X | isSubbase (get op) }.
Arguments sopen_cover {X} {open}.

Section Base.
Context {X:Type}.

(* Obvious lemmas *)
Property topology_is_base (T: Topology X): isBase (open(T)).
Proof with (auto with sets). split.
  - exists ( {|' Full_set X '|} ).
    split. intros S []. apply (open_empty_total(getPr T)). red...
  - intros. exists (U //\\ V). split... apply (open_intersect(getPr T))...
Qed.

Property base_is_subbase (B: Basis X): isSubbase (gopen(B)).
Proof with (auto with sets). split. apply (bopen_cover(getPr B)). Qed.

(* Generation *)
Definition topoFromBase (B: Basis X): PowerEn X :=
  fun U => forall x, x :in: U -> ExistsIn (gopen B) (fun S => x :in: S /\ S <:= U).

Program Definition topoFromBase_ (B: Basis X): Powerset X := exist _ (topoFromBase B) _.
Next Obligation. do 3 red. unfold topoFromBase. intros. unfold ExistsIn. rw_refl. Qed.

Lemma base_is_open: forall (B: Basis X), gopen B <:= topoFromBase B.
Proof. intros ? S ? ? ?. exists S. auto with sets. Qed.

Property generate_by_base (B: Basis X): isTopology (topoFromBase B).
Proof with (eauto with sets). split; unfold topoFromBase.
- (* Empty & Full *)
  split; try contradiction.
  destruct (bopen_cover(getPr B)) as [C [? HC]].
  intros ? [U []]%HC %unions_iff. exists U. split... apply H...
- (* Unions *)
  intros ? H ? [U [I0 I1]]%unions_iff. apply H in I1 as HE... clear H.
  destruct HE as [S (? & ? & ?)]. exists S. repeat split...
- (* Intersection *)
  intros ? ? HU HV ? [IU IV]%intersection_iff.
  specialize (HU _ IU) as [S (HU1 & HU2 & HU3)]. specialize (HV _ IV) as [T (HV1 & HV2 & HV3)].
  destruct (bopen_intersect(getPr B) _ _ x HU1 HV1) as [W (H1 & H2 & H3)]...
  exists W. split... split; auto. etransitivity...
Qed.

Lemma open_iff_base_unions: forall (B: Basis X),
  topoFromBase B '= indexed F in PSeton (gopen B), Unions F.
Proof with (eauto with sets).
  intros. intros U. rewrite indexed_iff. split.
  - (* <:= *)
    intros H.
    exists (unions x in U, (fun S => S :in: gopen B /\ x :in: S /\ S <:= U)). split.
    + do 2 red. apply inc_forall_unionover_iff. firstorder.
    + apply same_set_eq. split.
      * apply inc_forall_unions_iff. intros S [x [? (? & ? & ?)]]%unionover_iff...
      * intros x Hx. rewrite unions_unionover. apply unionover_iff. exists x. split...
        apply unions_iff. apply H in Hx as [S ?]. exists S. split... tauto.
  - (* =:> *)
    intros [F (? & E%symmetry)].
    eapply (getPr (topoFromBase_ B))... simpl. do 2 red in H.
    apply (open_union (generate_by_base B)). intros ? ?. apply base_is_open...
Qed.


Definition baseFromSubbase (S: Subbasis X): Ensemble X -> Prop :=
  fun V => exists (L: list (Ensemble X)), List.Forall (gopen(S)) L /\ V '= IntersectList L.

Program Definition baseFromSubbase_ (S: Subbasis X): Powerset X := exist _ (baseFromSubbase S) _.
Next Obligation. do 3 red. intros. unfold baseFromSubbase. rw_refl. Qed.

Property generate_by_subbase (S: Subbasis X): isBase (baseFromSubbase S).
Proof with (auto with sets).
  split.
  - (* Covers *)
    destruct (sopen_cover(getPr S)) as [C []]. exists C. split... unfold ForallIn.
    intros U A. exists (cons U nil). unfold gopen.
    split... unfold IntersectList...
  - (* Intersects *)
    intros ? ? ? [LU (AU & EU)] [LV (AV & EV)] HI. exists (U //\\ V).
    split... unfold baseFromSubbase.
    exists (app LU LV). split; [ apply List.Forall_app | ]...
    rewrite EU, EV. clear AU AV EU EV.
    induction LU; unfold app, IntersectList;
    [ rewrite intersection_comm | rewrite <- IHLU ]...
Qed.

Definition topoByBase (B: Basis X): Topology X := exist _ (topoFromBase_ B) (generate_by_base B).
Definition baseBySubbase (S: Subbasis X): Basis X := exist _ (baseFromSubbase_ S) (generate_by_subbase S).

(* TODO Better reduction property for indexed *)
(* Topology generated by Basis / Subbasis is minimal -> so it is unique *)
Lemma basis_gen_minimal: forall (B: Basis X) (T: Topology X),
  gopen(B) <:= open(T) -> open(topoByBase B) <:= open(T).
Proof.
  intros ? ? H. unfold topoByBase, open. simpl.
  rewrite open_iff_base_unions. intros U [F (? & ?%symmetry)]%(indexed_iff (PowerEn X)).
  pose proof (K := getPr (get T)); simpl in K. eapply K; eauto.
  apply (open_union (getPr T)). firstorder.
Qed.

Lemma subbasis_gen_minimal: forall (S: Subbasis X) (T: Topology X),
  gopen(S) <:= open(T) -> gopen (topoByBase (baseBySubbase S)) <:= open(T).
Proof.
  intros ? ? H. apply basis_gen_minimal.
  unfold baseBySubbase, gopen. simpl. intros F [G (H1 & H2)].
  pose proof (K := getPr (get T)); simpl in K. eapply K; eauto. clear H2 K.
  induction G as [| W G]; simpl.
  - apply (open_empty_total(getPr T)).
  - inversion H1; subst. apply (open_intersect (getPr T)); auto. firstorder.
Qed.

End Base.


(* ----------------------------------------------------------------- *)
(*                       Subspace Topology                           *)
(* ----------------------------------------------------------------- *)

(* Subspace topology *)
Section Subspace.
Context {X:Type}.
Context (T: Topology X) (A: Ensemble X).

Definition subspCorr: Ensemble (Subset A) -> Ensemble X -> Prop :=
  fun U V => U '= InvIm V incl.
Definition subspOpen: Ensemble (Subset A) -> Prop :=
  fun U => exists V, open(T) V /\ subspCorr U V.

Program Definition subspOpen_: Powerset (Subset A) := exist _ subspOpen _.
Next Obligation. do 3 red. unfold subspOpen, subspCorr. intros. rw_refl. Qed.

(* TODO subspace using basis *)
Property subspace_topo: isTopology subspOpen.
Proof with (eauto with sets).
  split; unfold subspOpen.
  - (* empty & full *)
    unfold subspCorr. split.
    + exists (Empty_set _). split... apply (open_empty_total (getPr T)).
    + exists (Full_set _). split... apply (open_empty_total (getPr T)).

  - (* unions *)
    intros. exists (unions U in M, unions V in (open(T) //\\ subspCorr U), V). split.
    + apply (open_union (getPr T)). apply forall_im_iff. intros ? ?.
      apply (open_union (getPr T)). apply forall_im_iff. intros ? []...
    + red. rewrite <- unions_as_over.
      rewrite invim_unionover. apply unionover_mor. intros U [? []]%H.
      rewrite invim_unionover. apply same_set_eq.
      split; [apply inced_forall_then_inced_unionover | apply inc_forall_unionover_iff];
      try (intros ? []; firstorder). eexists...

  - (* intersection *)
    unfold subspCorr. intros U U' [V [HV1 HV2]] [V' [HV'1 HV'2]].
    exists (V //\\ V').
    split; [apply (open_intersect (getPr T)) | all_rewrite ]...
Qed.

Definition SubspaceT: Topology (Subset A) := exist _ subspOpen_ subspace_topo.

Lemma open_subsp_open_whole: forall U: Ensemble (Subset A),
  open(T) A -> open(SubspaceT) U -> open(T) (Im U incl).
Proof with (eauto with sets).
  intros. repeat red in H0. destruct H0 as [V []]. unfold subspCorr in H1.
  assert (Im U incl '= A //\\ V); [rewrite H1|]...
  eapply (getPr (get T))... apply (open_intersect (getPr T))...
Qed.

End Subspace.

(* ----------------------------------------------------------------- *)
(*                        Product Topology                           *)
(* ----------------------------------------------------------------- *)

Section Product.
Context {X:Type} {Y:Type}.
Context (B: Topology X) (C: Topology Y).

Definition prodBasis: PowerEn (X * Y) :=
  indexed P in open(B) ** open(C), fst P ** snd P.
Definition prodBasis_: Powerset (X * Y) := exist _ prodBasis (properForm_spec _ _).

Property prod_basis: isBase prodBasis.
Proof with (eauto with sets).
  split; unfold prodBasis.
  - (* Covers *)
    exists ( {|' Full_set (X * Y) '|} ). split.
    + intros ? []. exists (Full_set X ** Full_set Y). split... econstructor. split.
      apply (open_empty_total(getPr B)). apply (open_empty_total(getPr C)). reflexivity.
    + red...
  - (* Intersection *)
    intros T1 T2 x [T1' [H1 E1]] [T2' [H2 E2]] H.
    exists (T1' //\\ T2'). split; [| all_rewrite]...
    apply im_iff in H1 as [(U1, V1) [[HU1 HV1]%prod_iff ?]].
    apply im_iff in H2 as [(U2, V2) [[HU2 HV2]%prod_iff ?]]. subst.
    pose proof (H1 := open_intersect (getPr B) _ _ HU1 HU2).
    pose proof (H2 := open_intersect (getPr C) _ _ HV1 HV2).
    eexists. split...
Qed.

Definition ProductB: Basis (X * Y) := exist _ prodBasis_ prod_basis.
Definition ProductT: Topology (X * Y) := topoByBase ProductB.


End Product.

End ToposSet.

