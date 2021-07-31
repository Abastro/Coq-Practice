Require Import Basics.
Require Import Setoid.
Require Import RelationClasses.

Require Import Ensembles.
Require Import Constructive_sets.

Require Import Fin.
Require List.

From Practice Require Import Base.
From Practice Require Import Functions.
From Practice Require Import Sets.
From Practice Require Import Image.

Definition Fin := Fin.t.

Module ToposSet.
Import Function_Extras.
Import Set_Extras.
Import Images.

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

(* Topology on Basis *)
Module TopoBasis.
Definition gopen {X:Type} {P: Powerset X -> Prop} (G: sig P): Ensemble X -> Prop := get (get G).

Record IsBase {X:Type} (open: Ensemble X -> Prop) : Type := {
  bopen_cover: exists (C: PowerEn X), ForallIn C open /\ cover_all C
; bopen_intersect: forall (U V: Ensemble X) x,
  open U -> open V -> x :in: U //\\ V -> exists W, open W /\ x :in: W /\ (W <:= U //\\ V)
}.
Definition Base (X:Type) := { op: Powerset X | IsBase (get op) }.
Arguments bopen_cover {X} {open}.
Arguments bopen_intersect {X} {open}.

Record IsSubbase {X:Type} (open: Ensemble X -> Prop) : Type := {
  sopen_cover: exists (C: PowerEn X), ForallIn C open /\ cover_all C
}.
Definition Subbase (X:Type) := { op: Powerset X | IsSubbase (get op) }.
Arguments sopen_cover {X} {open}.

Section OnSet.
Context {X:Type}.

Definition baseCorr: Ensemble X -> PowerEn X -> Prop := fun U F => U ~~ Unions F.
Definition topoFromBase (B: Base X): Ensemble X -> Prop :=
  fun U => exists (F: PowerEn X), ForallIn F (gopen(B)) /\ U ~~ Unions F.
Property topoFromBase_proper (B: Base X): properPset (topoFromBase B).
Proof. unfold properPset. unfold Morphisms.Proper, Morphisms.respectful.
  intros U V H. unfold topoFromBase. rw_refl. Qed.
Local Definition topoFromBase_ (B: Base X): Powerset X := exist _ _ (topoFromBase_proper B).

(* Quite long, require better abstraction *)
Property generate_by_base (B: Base X): isTopology (topoFromBase B).
Proof with (eauto with sets). split.
  - (* Empty & Full *)
    split; unfold topoFromBase.
    + exists (Empty_set _). split; [firstorder|]. symmetry...
    + destruct (bopen_cover(getPr B)) as [? [? C]]. unfold cover_all, covers in C...
  - (* Unions is open *)
    intros. unfold topoFromBase.
    set (N := unions U in M, unions F in PSeton (gopen B) //\\ baseCorr U, F). exists N. split.
    + intros V HV. unfold N in HV. apply unionover_iff in HV as [U [H1 HV]].
      apply unionover_iff in HV as [? [[? H0] HV]]. apply H0...
    + unfold N. rewrite unions_unionover. rewrite <- unions_as_over.
      apply unionover_mor. unfold gen_ext_eq. intros U HU. apply H in HU as [F [H0 H1]].
      apply eq_set_prop. split; intros HA.
      * rewrite H1 in HA. rewrite unions_iff in *. destruct HA as [? []]. eexists.
        split... apply unionover_iff...
      * apply unions_iff in HA as [? [HA ?]]. apply unionover_iff in HA as [? [[? ? HA] ?]].
        unfold baseCorr, In in HA. rewrite HA...
  - (* Intersection is open *)
    intros ? ? [FU (HU1 & HU2)] [FV (HV1 & HV2)]. unfold topoFromBase.
    set (N := gopen(B) //\\ PSeton (U //\\ V)). exists N.
    split; try (intros ? [])... unfold N. split.
    + rewrite HU2, HV2. unfold Included. intros ? [x KU KV]. rewrite unions_iff in *.
      destruct KU as [U1 (KU1 & KU2)]. destruct KV as [V1 (KV1 & KV2)].
      assert (E: exists W, gopen(B) W /\ x :in: W /\ U1 //\\ V1 =:> W).
      { apply (bopen_intersect(getPr B))... apply HU1... apply HV1... }
      destruct E as [W (H1 & H2 & H3)]. exists W. split... split...
      unfold PSeton, In. etransitivity...
    + apply inc_forall_unions_iff. intros ? [W ? ?]. firstorder.
Qed.

Definition baseFromSubbase (S: Subbase X): Ensemble X -> Prop :=
  fun V => exists (L: list (Ensemble X)), List.Forall (gopen(S)) L /\ V ~~ IntersectList L.
Property baseFromSubbase_proper (S: Subbase X): properPset (baseFromSubbase S).
Proof. unfold properPset. unfold Morphisms.Proper, Morphisms.respectful.
  intros U V H. unfold baseFromSubbase. rw_refl. Qed.
Local Definition baseFromSubbase_ (S: Subbase X): Powerset X := exist _ _ (baseFromSubbase_proper S).

Property generate_by_subbase (S: Subbase X): IsBase (baseFromSubbase S).
Proof with (auto with sets).
  split.
  - (* Covers *)
    destruct (sopen_cover(getPr S)) as [C []]. exists C. split... unfold ForallIn.
    intros U A. exists (cons U nil). unfold gopen. split... symmetry.
    unfold IntersectList...
  - (* Intersects *)
    intros ? ? ? [LU (AU & EU)] [LV (AV & EV)] HI. exists (U //\\ V). split...
    unfold baseFromSubbase. exists (app LU LV). split. { apply List.Forall_app... }
    rewrite EU, EV. clear AU AV EU EV. induction LU; simpl.
    { rewrite intersection_comm... } { rewrite <- IHLU. symmetry... }
Qed.

Definition topoByBase (B: Base X): Topology X := exist _ (topoFromBase_ B) (generate_by_base B).
Definition baseBySubbase (S: Subbase X): Base X := exist _ (baseFromSubbase_ S) (generate_by_subbase S).

End OnSet.

Lemma basis_gen_minimal: forall X (B: Base X) (T: Topology X),
  gopen(B) <:= open(T) -> open(topoByBase B) <:= open(T).
Proof.
  intros ? ? ? H. unfold Included. intros U H1. destruct H1 as [F [H1 H2]].
  pose proof (K := getPr (get T)); simpl in K. eapply K; eauto.
  apply (open_union (getPr T)). firstorder.
Qed.

Lemma subbasis_gen_minimal: forall X (S: Subbase X) (T: Topology X),
  gopen(S) <:= open(T) -> gopen (topoByBase (baseBySubbase S)) <:= open(T).
Proof.
  intros ? ? ? H. unfold Included. intros U H1. destruct H1 as [F [H1 H2]].
  pose proof (K := getPr (get T)); simpl in K. eapply K; eauto. clear H2.
  apply (open_union (getPr T)).
  assert (Claim: ForallIn F (fun V => gopen(baseBySubbase S) V -> open(T) V)). {
    unfold ForallIn. intros V L L1. destruct L1 as [G [L1 L2]]. eapply K; eauto. clear L2.
    clear H1. induction G as [| W G]; simpl.
    - (* empty case *) apply (open_empty_total (getPr T)).
    - (* inductive case *)
      inversion L1; subst. apply (open_intersect (getPr T)); auto; firstorder.
  }
  unfold ForallIn in *. intros. apply Claim; auto.
Qed.

End TopoBasis.

(* Subspace topology *)
Definition Subsp {X:Type} (A: Ensemble X): Type := { x: X | A x }.

Section Subspace.
Context {X:Type}.
Context (T: Topology X) (A: Ensemble X).

(* {get} serves as an inclusion A->X *)
Definition subspCorr: Ensemble (Subsp A) -> Ensemble X -> Prop := fun U V => U ~~ InvIm V get.
Definition subspOpen: Ensemble (Subsp A) -> Prop :=
  fun U => exists V, open(T) V /\ subspCorr U V.
Property subspace_proper: properPset subspOpen.
Proof. unfold properPset, Morphisms.Proper, Morphisms.respectful.
  unfold subspOpen. intros. unfold ExistsIn. unfold subspCorr. rw_refl. Qed.
Local Definition subspOpen_: Powerset (Subsp A) := exist _ _ subspace_proper.

Property subspace_topo: isTopology subspOpen.
Proof with (eauto with sets). split.
  - (* empty & full *)
    unfold subspOpen, subspCorr. split.
    + exists (Empty_set _). split. apply (open_empty_total (getPr T)). symmetry...
    + exists (Full_set _). split. apply (open_empty_total (getPr T)). symmetry...
  - (* unions *)
    unfold subspOpen. intros.
    set (N := unions U in M, unions V in (open(T) //\\ subspCorr U), V). exists N. split.
    + apply (open_union (getPr T)). intros ? H1. inversion H1; subst.
      apply (open_union (getPr T)). intros ? H2. inversion H2; subst. destruct H3...
    + unfold subspCorr. rewrite <- unions_as_over. unfold N.
      rewrite invim_unionover. apply unionover_mor. intros U MU.
      rewrite invim_unionover. apply eq_set_prop. intros. rewrite unionover_iff.
      unfold ExistsIn. setoid_rewrite intersection_iff. apply H in MU as EV. split; intros H0.
      * destruct EV. eexists. split... firstorder.
      * destruct H0 as [? [[H0 H1] H2]]. firstorder.
  - (* intersection *)
    unfold subspOpen, subspCorr. intros U U' [V [HV1 HV2]] [V' [HV'1 HV'2]]. exists (V //\\ V').
    split; try (apply (open_intersect (getPr T)); assumption).
    all_rewrite. symmetry...
Qed.

Definition SubspaceT: Topology (Subsp A) := exist _ subspOpen_ subspace_topo.

End Subspace.

End ToposSet.




