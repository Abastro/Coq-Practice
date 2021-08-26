(* ----------------------------------------------------------------- *)
(*                       Topological Spaces                          *)
(*                                                                   *)
(*  Based on Topology textbook by Munkres.                           *)
(* ----------------------------------------------------------------- *)

From Practice Require Import Basin.Base.
From Practice Require Import Basin.ElemAlg.
From Practice Require Import Basin.ClassicalSets.
From Practice Require Import Basin.ClSetLists.
Import List.
Import ListNotations.

(* Topology-like structure over type X *)
Record Topolike X (F: Powerset X -> Prop) := mkTopo{
  opens: Powerset X
; topo_proper: ProperSet opens
; topo_cond: F opens
}.

Arguments mkTopo {X F}.
Arguments opens {X F}.
Arguments topo_proper {X F}.
Arguments topo_cond {X F}.

Property mkTopo_spec: forall X (F: Powerset X -> Prop) (C: Powerset X),
  ProperSet C -> F C -> exists T: Topolike X F, opens T = C.
Proof. intros * HP HC. exists (mkTopo C HP HC). reflexivity. Qed.

Program Instance setoid_topo X F: Setoid (Topolike X F) := {
  equiv := (fun T T' => opens T == opens T')
}.
Next Obligation. firstorder. Qed.

Instance proper_opens X F (T: Topolike X F): ProperSet (opens(T)).
Proof. apply topo_proper. Qed.


(* Closed sets: all those where its complement is open *)
Definition closes {X F} (T: Topolike X F): Powerset X :=
  mkSet (fun E => ~! E :in: opens(T)).

Instance proper_closes X F (T: Topolike X F): ProperSet (closes(T)).
Proof. intros ? **. unfold closes, InSet. rw_refl. Qed.


Notation "'open' [ T ]" := (InSet (opens T))
  (format "'open' [ T ]").
Notation "'closed' [ T ]" := (InSet (closes T))
  (format "'closed' [ T ]").


Record isTopology {X} (opens: Powerset X): Prop := {
  union_open: forall M: Powerset X,
    M <:= opens -> Unions M :in: opens
; intersect_open: forall L: list (ESet X),
    Forall (InSet opens) L -> MCat Intersect L :in: opens
}.
Definition Topology X := Topolike X isTopology.
Arguments union_open {X} {opens}.
Arguments intersect_open {X} {opens}.


Definition covers {X} (V: ESet X) (C: Powerset X): Prop :=
  V <:= Unions C.
Notation cover_all := (covers FullSet).


(* ----------------------------------------------------------------- *)
(*                       General Properties                          *)
(* ----------------------------------------------------------------- *)

Section Topo.
Context {X:Type} (T: Topology X).

(* Property of open sets *)
Property unions_is_open: forall M: Powerset X,
  ForallIn M (open[T]) -> open[T] (Unions M).
Proof. apply union_open, topo_cond. Qed.

Property intersects_is_open: forall L: list (ESet X),
  Forall (open[T]) L -> open[T] (MCat Intersect L).
Proof. apply intersect_open, topo_cond. Qed.

Property empty_is_open: open[T] EmptySet.
Proof. rewrite <- unions_empty.
  apply unions_is_open. intros ? []. Qed.

Property full_is_open: open[T] FullSet.
Proof. replace (@FullSet X) with (MCat (@Intersect X) []) by reflexivity.
  apply intersects_is_open. trivial. Qed.


Lemma union_is_open: forall U V: ESet X,
  open[T] U -> open[T] V -> open[T] (U \\// V).
Proof. intros.
  rewrite <- unions_couple. apply unions_is_open.
  intros ? [K|K]; do 2 red in K; rewrite <- K; auto.
Qed.

Lemma intersect_is_open: forall U V: ESet X,
  open[T] U -> open[T] V -> open[T] (U //\\ V).
Proof. intros.
  rewrite <- mcat_couple. apply intersects_is_open.
  repeat constructor; auto.
Qed.


Lemma unionover_is_open: forall I (P: ESet I) (F: I -> ESet X),
  ForallIn P (fun i => open[T] (F i)) -> open[T] (unions i in P, F i).
Proof. intros * H. apply unions_is_open.
  intros _ (i & ? & ->). apply H. trivial. Qed.

Lemma intersectover_is_open: forall I (L: list I) (F: I -> ESet X),
  Forall (fun i => open[T] (F i)) L -> open[T] (MCatOver Intersect F L).
Proof. intros * H. apply intersects_is_open.
  rewrite Forall_forall in *.
  intros _ (i & <- & ?)%in_map_iff. apply H. trivial. Qed.

(* Property of closed sets *)
Property intersects_is_closed: forall M: Powerset X,
  ForallIn M (closed[T]) -> closed[T] (Intersects M).
Proof. intros. do 3 red.
  rewrite intersects_as_over, intersectover_compl.
  apply unionover_is_open. trivial. Qed.

Property unions_is_closed: forall L: list (ESet X),
  Forall (closed[T]) L -> closed[T] (MCat Union L).
Proof. intros. do 2 red.
  rewrite cat_unions_as_unionover, cat_unionover_compl.
  apply intersectover_is_open. trivial. Qed.

Property empty_is_closed: closed[T] EmptySet.
Proof. do 3 red. rewrite empty_compl. apply full_is_open. Qed.

Property full_is_closed: closed[T] FullSet.
Proof. do 3 red. rewrite full_compl. apply empty_is_open. Qed.


Lemma intersect_is_closed: forall U V: ESet X,
  closed[T] U -> closed[T] V -> closed[T] (U //\\ V).
Proof. intros. do 2 red. rewrite intersect_compl.
  apply union_is_open; trivial. Qed.

Lemma union_is_closed: forall U V: ESet X,
  closed[T] U -> closed[T] V -> closed[T] (U \\// V).
Proof. intros. do 2 red. rewrite union_compl.
  apply intersect_is_open; trivial. Qed.


Lemma intersectover_is_closed: forall I (P: ESet I) (F: I -> ESet X),
  ForallIn P (fun i => closed[T] (F i)) -> closed[T] (intersects i in P, F i).
Proof. intros * H. apply intersects_is_closed.
  intros _ (i & ? & ->). apply H. trivial. Qed.

Lemma unionover_is_closed: forall I (L: list I) (F: I -> ESet X),
  Forall (fun i => closed[T] (F i)) L -> closed[T] (MCatOver Union F L).
Proof. intros * H. apply unions_is_closed.
  rewrite Forall_forall in *.
  intros _ (i & <- & ?)%in_map_iff. apply H. trivial. Qed.

End Topo.


(* ----------------------------------------------------------------- *)
(*                         Topology Basis                            *)
(* ----------------------------------------------------------------- *)

Record isBase {X} (opens: Powerset X): Type := {
  bopen_cover: exists (C: Powerset X), C <:= opens /\ cover_all C
; inter_refine_open: forall (U V: ESet X) x,
  U :in: opens -> V :in: opens -> x :in: U //\\ V ->
  exists W, W :in: opens /\ x :in: W /\ (W <:= U //\\ V)
}.
Definition Basis X := Topolike X isBase.
Arguments bopen_cover {X} {opens}.
Arguments inter_refine_open {X} {opens}.

Definition Subbasis X := Topolike X (const True).

Section Base.
Context {X:Type}.

Property topology_is_base (T: Topology X): isBase (opens(T)).
Proof with (auto with sets). split.
  - unfold covers. exists (opens(T)). split... apply unions_inc_one, full_is_open.
  - intros. exists (U //\\ V). split... apply intersect_is_open...
Qed.


(* Generation *)
Program Definition topoFromBase (B: Powerset X): Powerset X :=
  mkSet (fun U => forall x, x :in: U ->
    ExistsIn B (fun V => x :in: V /\ V <:= U)).

Global Instance proper_topoFromBase (B: Powerset X): ProperSet (topoFromBase B).
Proof. intros ? **. unfold topoFromBase, ExistsIn. rewrite mkSet_In. rw_refl. Qed.

Lemma base_is_open: forall B, B <:= topoFromBase B.
Proof. firstorder. Qed.

Proposition generate_by_base (B: Basis X): isTopology (topoFromBase (opens B)).
Proof with firstorder.
  unfold topoFromBase. split; rewrite mkSet_In.
  - (* Unions *)
    intros ? H ? (U & I1 & I2)%unions_iff.
    specialize (H _ I1 _ I2)...
  - (* Intersects *)
    intros ? H ?. pose proof (topo_cond B) as (HC & HR).
    apply mcat_ind.
    + (* Full set *)
      destruct HC as (C & HI & HC).
      intros (U & HU & Hx) %HC %unions_iff...
    + (* Intersect-2 *)
      intros U V HU HV ([S (HU1 & HU2 & HU3)]%HU & [T (HV1 & HV2 & HV3)]%HV).
      destruct (HR _ _ x HU1 HV1) as [W (H1 & H2 & H3)]...
    + clear HC HR. rewrite Forall_forall in *...
Qed.

Lemma open_iff_base_unions: forall (B: Basis X),
  topoFromBase (opens B) == {' Unions F | F in PsetOn (opens B) '}.
Proof with firstorder.
  intros ? U. split.
  - (* <:= *)
    intros H.
    exists (unions x in U,
      mkSet(fun S => S :in: opens(B) /\ x :in: S /\ S <:= U)). split.
    + do 4 red...
    + rewrite unions_unionover. apply same_inc_iff. split.
      * intros x Hx. apply unionover_iff...
      * apply inc_forall_unionover_iff...
  - (* =:> *)
    intros [F (? & ->)]. do 4 red in H.
    apply (union_open (generate_by_base B))...
Qed.


Definition baseFromSubbase (S: Powerset X): Powerset X :=
  {' MCat Intersect L | L in ForallSet S '}.

Lemma subbase_is_base_open: forall S, S <:= baseFromSubbase S.
Proof. intros ? B ?. exists [B]. firstorder. simpl. repeat constructor. auto. Qed.

Lemma subbase_is_open: forall S, S <:= topoFromBase (baseFromSubbase S).
Proof. etransitivity. apply subbase_is_base_open. apply base_is_open. Qed.

Proposition generate_by_subbase (S: Subbasis X): isBase (baseFromSubbase (opens S)).
Proof with (auto with sets alg).
  split.
  - (* Covers *)
    unfold covers. exists {{FullSet}}. split...
    intros U <-%singleton_iff. exists []. split... simpl...
  - (* Intersects *)
    intros ? ? ? [LU (AU & EU)] [LV (AV & EV)] HI.
    exists (U //\\ V). split... apply im_iff.
    exists (LU ++ LV). split; [ apply Forall_app | ]...
    rewrite EU, EV...
Qed.

Program Definition topoByBase (B: Basis X): Topology X := mkTopo (topoFromBase (opens B)) _ _.
Next Obligation. apply generate_by_base. Qed.

Program Definition baseBySubbase (S: Subbasis X): Basis X := mkTopo (baseFromSubbase (opens S)) _ _.
Next Obligation. apply generate_by_subbase. Qed.

(*  Denotes is that certain powerset serves as a base of the topology *)
Definition isBaseOf (C: Powerset X) (T: Topology X): Prop :=
  exists B: Basis X, opens(B) = C /\ topoByBase B == T.
Definition isSubbaseOf (C: Powerset X) (T: Topology X): Prop :=
  exists S: Subbasis X, opens(S) = C /\ topoByBase (baseBySubbase S) == T.

Property isBase_then_generate: forall C T,
  isBaseOf C T -> topoFromBase C == opens(T).
Proof. intros * (? & <- & ?). trivial. Qed.

Property isSubbase_then_generate: forall C T,
  isSubbaseOf C T -> topoFromBase (baseFromSubbase C) == opens(T).
Proof. intros * (? & <- & ?). trivial. Qed.


(* Topology generated by Basis / Subbasis is minimal -> so it is unique *)
Lemma basis_gen_minimal: forall (B: Basis X) (T: Topology X),
  opens(B) <:= opens(T) -> opens(topoByBase B) <:= opens(T).
Proof.
  intros **. unfold topoByBase. simpl.
  rewrite open_iff_base_unions. intros U [F (H0 & ->)].
  apply unions_is_open. firstorder.
Qed.

Lemma subbasis_gen_minimal: forall (S: Subbasis X) (T: Topology X),
  opens(S) <:= opens(T) -> opens(topoByBase (baseBySubbase S)) <:= opens(T).
Proof.
  intros **. apply basis_gen_minimal.
  unfold baseBySubbase. simpl. intros U [L (H1 & ->)].
  apply intersects_is_open. simpl in H1.
  rewrite Forall_forall in *. firstorder.
Qed.

Lemma identify_base: forall (T: Topology X) (C: Powerset X) `(@ProperSet _ (setoid_set _) C),
  C <:= opens(T) ->
  ForallIn (opens T) (fun U =>
    forall x, x :in: U -> ExistsIn C (fun V => x :in: V /\ V <:= U)) ->
  isBaseOf C T.
Proof with (auto with sets).
  intros * HP HI H. destruct (mkTopo_spec _ isBase C) as [B ?].
  - apply HP.
  - (* Is Basis *) split.
    + (* Cover *)
      exists C. split... unfold cover_all.
      intros x [V (? & ? & ?)]%H. firstorder.
      apply full_is_open.
    + (* Intersection *)
      intros * HU%HI HV%HI IN.
      apply H... apply intersect_is_open...
  - (* Generates *)
    exists B. split; subst... apply same_inc_iff. simpl.
    split... apply basis_gen_minimal...
Qed.

End Base.


(* ----------------------------------------------------------------- *)
(*                     Continuity & Homeomorphism                    *)
(* ----------------------------------------------------------------- *)

Definition Continuous {X Y} (S: Topology X) (T: Topology Y) (f: X -> Y): Prop :=
  ForallIn (opens(T)) (fun V => InvIm f V :in: opens(S)).

Notation "f ':-' S '~>' T" := (Continuous S T f)
  (at level 75, no associativity).

Add Parametric Morphism X Y: (@Continuous X Y)
  with signature equiv ==> equiv ==> eq ==> iff as conti_mor.
Proof. firstorder. Qed.


Property conti_as_set: forall X Y (S: Topology X) (T: Topology Y) (f: X -> Y),
  (f :- S ~> T) <-> ({' InvIm f V | V in opens(T) '} <:= opens(S)).
Proof. intros. split.
  - intros H _ (V & ? & ->). apply H. trivial.
  - intros H V HV. apply H. apply im_def. trivial.
Qed.


Lemma basis_invim_conti: forall X Y (S: Topology X) (B: Basis Y) (f: X -> Y),
  ForallIn (opens(B)) (fun V => open[S] (InvIm f V)) ->
  f :- S ~> topoByBase B.
Proof.
  intros ** V (F & HV1 & ->)%open_iff_base_unions.
  rewrite unions_as_over, invim_unionover.
  apply unionover_is_open. firstorder.
Qed.

Lemma subbasis_invim_conti: forall X Y (S: Topology X) (B: Subbasis Y) (f: X -> Y),
  ForallIn (opens(B)) (fun V => open[S] (InvIm f V)) ->
  f :- S ~> topoByBase (baseBySubbase B).
Proof.
  intros **. apply basis_invim_conti.
  intros _ (L & HL & ->). induction L.
  - simpl. rewrite invim_full. apply full_is_open.
  - simpl. rewrite invim_intersect.
    inversion HL; subst.
    apply intersect_is_open; firstorder.
Qed.


Section ConstrConti.
Context {X Y Z: Type} (R: Topology X) (S: Topology Y) (T: Topology Z).

Lemma const_conti: forall (y: Y), (const y) :- R ~> S.
Proof. intros ** U HU. decides (y :in: U) as [H|H].
  - eapply proper_opens; [| apply full_is_open]. firstorder.
  - eapply proper_opens; [| apply empty_is_open]. firstorder.
Qed.

Lemma id_conti: id :- R ~> R.
Proof. intros U. rewrite invim_identity. easy. Qed.

Lemma compose_conti: forall f g,
  (f :- R ~> S) -> (g :- S ~> T) -> compose g f :- R ~> T.
Proof. intros * Hf Hg U HU.
  rewrite invim_compose. apply Hf, Hg, HU. Qed.

End ConstrConti.


Section UsualMap.
Context {X Y: Type} `{D: UsualSetoid Y}.

Definition OpenMap (S: Topology X) (T: Topology Y) (f: X -> Y): Prop :=
  ForallIn (opens(S)) (fun U => open[T] (Im f U)).

Definition Homeomorphism (S: Topology X) (T: Topology Y) (f: X -> Y): Prop :=
  bijective f /\ Continuous S T f /\ OpenMap S T f.

End UsualMap.

Notation "f ':-' S '~=' T" := (Homeomorphism S T f)
  (at level 75, no associativity).

Lemma homeo_bijective: forall X Y `(DX: UsualSetoid X) `(DY: UsualSetoid Y),
  forall (S: Topology X) (T: Topology Y) f g,
  compose f g == id -> compose g f == id -> 
  f :- S ~> T -> g :- T ~> S -> f :- S ~= T.
Proof with auto.
  intros * E1 E2 Hf Hg.
  assert (Bij: bijective f). { split.
    eapply left_inv_then_inj. apply E2.
    eapply right_inv_then_surj. apply E1.
  }
  split... split... (* Only open map is nontrivial *)
  intros U HU.
  setoid_replace (Im f U) with (InvIm g U). apply Hg...
  rewrite <- invim_identity, <- E1, invim_compose.
  eapply invim_mor... apply invim_of_im_eq_inj, Bij.
Qed.


(* ----------------------------------------------------------------- *)
(*                       Subspace Topology                           *)
(* ----------------------------------------------------------------- *)

(* Subspace topology *)
Section Subspace.
Context {X:Type} (T: Topology X) (A: ESet X).

Definition subsetOver (C: Powerset X): Powerset (Subset A) :=
  {' InvIm inclu U | U in C '}.

Proposition subspace_topo: isTopology (subsetOver (opens T)).
Proof with (auto with sets; firstorder).
  split; unfold subsetOver.
  - (* Unions *)
    intros. (* Need W s.t. Unions M == InvIm inclu W *)
    exists (Unions {: U in opens(T) | InvIm inclu U :in: properForm M :}). split.
    + apply unions_is_open. intros ? []...
    + symmetry. rewrite unions_as_over, invim_unionover.
      apply same_inc_iff; split.
      * apply inc_forall_unionover_iff...
      * apply inc_forall_unions_iff. intros V HV.
        specialize (H _ HV) as [U (? & E)]...
  - (* Intersects *)
    intros L. apply mcat_ind.
    + (* FullSet *)
      exists FullSet... apply full_is_open.
    + (* Intersect-2 *)
      intros U U' [V (HV1 & HV2)] [V' (HV'1 & HV'2)].
      exists (V //\\ V'). rewrite invim_intersect.
      split; [apply intersect_is_open | all_rewrite]...
Qed.

Program Definition SubspaceT: Topology (Subset A) := mkTopo (subsetOver (opens T)) _ _.
Next Obligation. apply subspace_topo. Qed.


Lemma subsp_basis_from_basis: forall C: Powerset X,
  isBaseOf C T -> isBaseOf (subsetOver C) SubspaceT.
Proof with (auto with sets).
  intros ? [B (<- & HE)]. do 2 red in HE. apply identify_base.
  - (* Proper *) exact _.
  - (* Contained in subspace topology *)
    apply im_inc. rewrite <- HE. apply base_is_open.
  - (* Forms basis of the topo *)
    intros V [U (HU%HE & EV)] y Hy%EV.
    specialize (HU (inclu y) Hy) as [W (? & ? & ?)].
    exists (InvIm inclu W). rewrite EV.
    split. apply im_def... split...
Qed.

(* Using usual equality *)
Section UsualEq.
Context `{UsualSetoid X}.

Lemma open_subsp_open_whole: forall U: ESet (Subset A),
  open[T] A -> open[SubspaceT] U -> open[T] (Im inclu U).
Proof with (auto with sets).
  intros * ? [V [? ->]]%im_iff.
  rewrite incl_im_of_invim. apply intersect_is_open...
Qed.

Lemma closes_subsp_is: closes(SubspaceT) == {' InvIm inclu E | E in closes(T) '}.
Proof with (auto with sets).
  intros E. split.
  - (* -> *)
    intros [U [H0 HE]]. exists (~! U).
    split. do 4 red. rewrite compl_compl...
    rewrite <- invim_compl, <- HE...
  - (* <- *)
    intros [F [HC HE]]. do 4 red in HC |- *.
    rewrite HE, invim_compl. apply im_def...
Qed.
Corollary closed_subsp_iff: forall (F: ESet (Subset A)),
  closed[SubspaceT] F <-> ExistsIn (closes(T)) (fun E => F == InvIm inclu E).
Proof. intros. rewrite closes_subsp_is. firstorder. Qed.

Lemma closed_subsp_closed_whole: forall (E: ESet (Subset A)),
  closed[T] A -> closed[SubspaceT] E -> closed[T] (Im inclu E).
Proof with (eauto with sets).
  intros * ?. rewrite closes_subsp_is.
  intros [F [? ->]]%im_iff.
  rewrite incl_im_of_invim. apply intersect_is_closed...
Qed.

End UsualEq.

(* Subspace and continuity *)

Lemma inclu_conti: inclu :- SubspaceT ~> T.
Proof. intros U HU. apply im_def. auto. Qed.

End Subspace.


(* Use local-continuity to prove continuity *)
Lemma localconti_conti: forall X Y (R: Topology X) (S: Topology Y),
  forall `(UsualSetoid X) f (P: Powerset X),
  P <:= opens(R) -> cover_all P ->
  ForallIn P (fun U => compose f inclu :- (SubspaceT R U) ~> S) ->
  f :- R ~> S.
Proof with (auto with sets).
  intros * ? * HO HC Hf V HV. set (fU U := compose f (@inclu _ U)).
  assert (E: forall U, InvIm f V //\\ U == Im inclu (InvIm (fU U) V)). {
    intros U. unfold fU.
    rewrite invim_compose, incl_im_of_invim...
  }
  assert (Claim: InvIm f V == unions U in P, Im inclu (InvIm (fU U) V)). {
    setoid_replace (InvIm f V) with (InvIm f V //\\ unions U in P, U).
    rewrite intersect_distr_unions. apply unionover_mor...
    firstorder.
  }
  rewrite Claim. apply unionover_is_open. intros U HU.
  apply open_subsp_open_whole. apply HO... apply Hf...
Qed.


(* Imbedding *)
Section UsualMap.
Context {X Y: Type} `{D: UsualSetoid Y}.

Program Definition imbed (f: X -> Y): X -> Subset (Im f FullSet) :=
  fun x => exist _ (f x) _.
Next Obligation. exists x. firstorder. Qed.

Definition Imbedding (S: Topology X) (T: Topology Y) (f: X -> Y): Prop :=
  let SubT := SubspaceT(T) (Im f FullSet) in
  imbed f :- S ~= SubT.

End UsualMap.


(* ----------------------------------------------------------------- *)
(*                        Product Topology                           *)
(* ----------------------------------------------------------------- *)

Section Product.
Context {X Y:Type}.
Context (S: Topology X) (T: Topology Y).

Definition prodOver (C: Powerset X) (D: Powerset Y): Powerset (X * Y) :=
  {' U ** V | '(U, V) in C ** D '}.

Property prodover_def: forall C D U V,
  U :in: C -> V :in: D -> (U ** V) :in: prodOver C D.
Proof. intros. exists (U, V). firstorder. Qed.


Proposition prod_basis: isBase (prodOver (opens S) (opens T)).
Proof with (eauto 3 with sets).
  split.
  - (* Covers *)
    exists {{FullSet}}. split.
    + intros _ <-%singleton_iff. rewrite <- full_prod.
      apply prodover_def; apply full_is_open.
    + red...
  - (* Intersection *)
    intros W1 W2 x [(U1, V1) [H1 E1]] [(U2, V2) [H2 E2]] H.
    exists (W1 //\\ W2). split; [| split]...
    destruct H1 as (HU1 & HV1), H2 as (HU2 & HV2).
    specialize (intersect_is_open _ _ _ HU1 HU2) as H1.
    specialize (intersect_is_open _ _ _ HV1 HV2) as H2.
    eexists (_, _). split... rewrite E1, E2...
Qed.

Program Definition ProductB: Basis (X * Y) := mkTopo (prodOver (opens S) (opens T)) _ _.
Next Obligation. apply prod_basis. Qed.

Definition ProductT: Topology (X * Y) := topoByBase ProductB.


Lemma prod_basis_from_basis: forall (B: Powerset X) (C: Powerset Y),
  isBaseOf B S -> isBaseOf C T ->
  isBaseOf (prodOver B C) ProductT.
Proof with (auto with sets).
  intros * [Bt (<- & EB)] [Ct (<- & EC)].
  apply identify_base.
  - exact _.
  - (* Contained in ProductT *)
    etransitivity; [| apply base_is_open].
    intros _ [(U, V) ([] & ->)].
    apply prodover_def; firstorder.
  - (* Forms basis of the topo *)
    intros W HW (x, y) Hxy.
    specialize (HW (x, y) Hxy) as [_ [[(U, V) (HI & ->)] (HR1 & HR2)]].
    destruct HI as (HU%EB & HV%EC), HR1 as (HU2 & HV2).
    specialize (HU x HU2) as [I (?&?&?)]. specialize (HV y HV2) as [J (?&?&?)].
    exists (I ** J). split. apply prodover_def...
    split... etransitivity; eauto...
Qed.


Lemma fst_conti: fst :- ProductT ~> S.
Proof with (auto with sets).
  intros * V HV. rewrite invim_fst_prod.
  apply base_is_open, prodover_def...
  apply full_is_open.
Qed.

Lemma snd_conti: snd :- ProductT ~> T.
Proof with (auto with sets).
  intros * V HV. rewrite invim_snd_prod.
  apply base_is_open, prodover_def...
  apply full_is_open.
Qed.


Definition prodSubbasis: Powerset (X * Y) :=
  {' InvIm fst U | U in opens S '} \\// {' InvIm snd V | V in opens T '}.

Theorem prod_subbasis_spec:
  isSubbaseOf prodSubbasis ProductT.
Proof with (eauto with sets).
  destruct (mkTopo_spec _ (const True) prodSubbasis) as [B HS].
  - (* Proper *) exact _.
  - (* Subbase, trivial *) apply I.
  - (* Generates exact *)
    exists B. split; auto. apply same_inc_iff. split.
    + (* open ProductT =:> *)
      apply subbasis_gen_minimal. rewrite HS.
      apply union_inc_split.
      split; apply conti_as_set. apply fst_conti. apply snd_conti.
    + (* open ProductT <:= *)
      apply basis_gen_minimal. etransitivity; [| apply base_is_open].
      intros _ [(U, V) ((HU & HV) & ->)]. apply im_iff.
      exists [InvIm fst U; InvIm snd V]. rewrite HS. split.
      * repeat apply Forall_cons; [left | right | constructor]...
      * rewrite mcat_couple...
Qed.


(* Checking continuous function into product space *)
Theorem product_map_conti: forall W (R: Topology W),
  forall f1 f2, let f := fun a => (f1 a, f2 a) in
  (f :- R ~> ProductT) <-> (f1 :- R ~> S) /\ (f2 :- R ~> T).
Proof with (auto with sets).
  intros. split.
  - (* -> *)
    intros H. split;
    [ replace f1 with (compose fst f) | replace f2 with (compose snd f) ]...
    all: eapply compose_conti; [apply H|].
    apply fst_conti. apply snd_conti.
  - (* <- *)
    intros (H1 & H2). apply basis_invim_conti.
    intros _ ((U, V) & [HU HV] & ->).
    assert (InvIm f (U ** V) == InvIm f1 U //\\ InvIm f2 V) as ->. {
      intros x. rewrite intersect_iff. rewrite 3 invim_iff. apply prod_iff. }
    apply intersect_is_open. apply H1... apply H2...
Qed.

End Product.


(* Homeomorphism btwn product of subspaces and subspace of products *)
(* TODO Rewrite *)
Theorem prod_subsp_exch: forall X Y `(DX: UsualSetoid X) `(DY: UsualSetoid Y),
  forall (S: Topology X) (T: Topology Y) (A: ESet X) (B: ESet Y),
  let SubA := SubspaceT(S) A in let SubB := SubspaceT(T) (B) in
  ps_to_sp :- ProductT SubA SubB ~= SubspaceT (ProductT S T) (A ** B).
Proof with auto.
  intros.
  (* Convert subspace of product space to use basis *)
  assert ( isBaseOf ( subsetOver (A ** B) ( prodOver (opens S) (opens T) ) )
      (SubspaceT (ProductT S T) (A ** B))
  ) as (BSP & HE & Rep).
  { apply subsp_basis_from_basis; exists (ProductB S T)... }

  (* TODO Set equal under bijection *)
  (* Basis elements are equal *)
  assert ( EQ: forall U V,
    InvIm ps_to_sp (InvIm (@inclu _ (A ** B)) (U ** V)) ==
    InvIm inclu U ** InvIm inclu V ).
  { intros * (x, y). rewrite prod_iff, 4 invim_iff. reflexivity. }

  assert (E1: compose ps_to_sp (@sp_to_ps _ _ A B) == id).
  { intros ?. apply sub_prod_id. }
  assert (E2: compose sp_to_ps (@ps_to_sp _ _ A B) == id).
  { intros ?. apply prod_sub_id. }

  eapply homeo_bijective with (g := sp_to_ps)...
  - (* ps_to_sp continuous *)
    rewrite <- Rep. apply basis_invim_conti. rewrite HE.
    intros _ (_ & ((U, V) & [HU HV] & ->) & ->).
    apply base_is_open.
    rewrite -> EQ.
    apply prodover_def... all: apply im_def...
  - (* sp_to_ps continuous *)
    rewrite <- Rep. apply basis_invim_conti.
    intros _ ((_, _) & [(U & HU & ->) (V & Hv & ->)] & ->).
    apply base_is_open. rewrite HE.
    rewrite <- EQ, <- invim_compose, E1, invim_identity.
    apply im_def. apply prodover_def...
Qed.


(* ----------------------------------------------------------------- *)
(*                 Basic Structure in a Topology                     *)
(* ----------------------------------------------------------------- *)

Section TopoStr.
Context {X:Type} (T: Topology X).

Definition Interior (A: ESet X): ESet X :=
  Unions {: U in opens(T) | U <:= A :}.
Definition Closure (A: ESet X): ESet X :=
  Intersects {: E in closes(T) | E =:> A :}.

Property interior_in: forall A, Interior A <:= A.
Proof. firstorder. Qed.

Property closure_out: forall A, Closure A =:> A.
Proof. firstorder. Qed.

Property interior_eq_iff: forall A, open[T] A <-> Interior A == A.
Proof. firstorder. rewrite <- H. apply unions_is_open. firstorder. Qed.

Property closure_eq_iff: forall A, closed[T] A <-> Closure A == A.
Proof. firstorder. rewrite <- H. apply intersects_is_closed. firstorder. Qed.

Property interior_open: forall A, open[T] (Interior A).
Proof. intros. apply unions_is_open. firstorder. Qed.

Property closure_closed: forall A, closed[T] (Closure A).
Proof. intros. apply intersects_is_closed. firstorder. Qed.


Property interior_inc_if: forall A B, A <:= B -> Interior A <:= Interior B.
Proof. intros ** x [U]. exists U. firstorder. Qed.

Property closure_inc_if: forall A B, A <:= B -> Closure A <:= Closure B.
Proof. intros ** x ? E []. apply H0. firstorder. Qed.

End TopoStr.

Notation "'Int' [ T ]" := (Interior T)
  (format "'Int' [ T ]").
Notation "'Cl' [ T ]" := (Closure T)
  (format "'Cl' [ T ]").

Lemma subspace_closure: forall X `(D: UsualSetoid X) T (Y: ESet X) (A: ESet (Subset Y)),
  let S := SubspaceT T Y in
  Cl[S] A == InvIm inclu (Cl[T] (Im inclu A)).
Proof with (auto with sets).
  intros. apply same_inc_iff. split.
  - (* Cl[S] A <:= Cl[T] A /\ Y *)
    set (E := Cl[T] (Im inclu A)).
    apply intersects_inced_one. split.
    apply closes_subsp_is, im_def, closure_closed.
    rewrite mkSet_In, <- (incl_invim_of_im _ A).
    apply invim_inc, closure_out.
  - (* Cl[S] A =:> Cl[T] A /\ Y *)
    set (B := Cl[S] A).
    assert (closed[S] B) as (C & HC & HE)%closed_subsp_iff by apply closure_closed...
    rewrite HE. apply invim_inc, intersects_inced_one.
    split... rewrite mkSet_In. transitivity (Y //\\ C)...
    rewrite <- incl_im_of_invim. apply im_inc.
    rewrite <- HE. apply closure_out.
Qed.


Lemma closure_intersects: forall X T (A: ESet X) x,
  x :in: Cl[T] A <-> ForallIn (opens(T)) (fun U => x :in: U -> Inhabited (A //\\ U)).
Proof with (auto with sets).
  split.
  - (* -> *)
    intros H U H1 H2. contra.
    apply not_inhabited_empty in contra.
    assert (I: A <:= ~! U). firstorder.
    specialize (H (~! U)). apply H...
    split... do 4 red. rewrite compl_compl...
  - (* <- *)
    intros H E [HC HI]. contra.
    specialize (H (~!E) HC contra) as []. firstorder.
Qed.
Corollary closure_intersects_basis: forall X S (A: ESet X) x,
  let T := topoByBase S in
  x :in: Cl[T] A <-> ForallIn (opens(S)) (fun B => x :in: B -> Inhabited (A //\\ B)).
Proof with (auto with sets).
  intros. etransitivity. apply closure_intersects. split.
  - intros H B ? ?. apply H... apply base_is_open...
  - intros H U HO [V (? & ? & ?)]%HO. firstorder.
Qed.


Definition Neighborhood {X} (T: Topology X) x: Powerset X :=
  {: U in opens(T) | x :in: U :}.

Notation "'nbhd' [ T ]" := (Neighborhood T)
  (format "'nbhd' [ T ]").

Corollary closure_nbhd: forall X T (A: ESet X) x,
  x :in: Cl[T] A <-> ForallIn (nbhd[T] x) (fun U => Inhabited (A //\\ U)).
Proof. intros. etransitivity. apply closure_intersects. firstorder. Qed.


(* Elaboration on continuity *)
Section MapToEq.
Context {X Y} `{D: UsualSetoid Y} (S: Topology X) (T: Topology Y) (f: X -> Y).

Theorem tfae_continuity:
  TFAE [
      Continuous S T f
    ; forall A: ESet X, Im f (Cl[S] A) <:= Cl[T] (Im f A)
    ; ForallIn (closes(T)) (fun E => InvIm f E :in: closes(S))
  ].
Proof with (auto 4 with sets).
  intros. tfae_chain.
  - (* 0 -> 1 *)
    intros H A _ (x & Hx & ->).
    rewrite -> closure_intersects in *.
    intros V HV1%H HV2%invim_iff.
    specialize (Hx _ HV1 HV2) as (y & ? & ?).
    exists (f y)...
  - (* 1 -> 2 *)
    intros H E HE%closure_eq_iff. apply closure_eq_iff.
    set (A := InvIm f E).
    apply same_inc_iff. split; [| apply closure_out].
    assert (HI: Im f (Cl[S] A) <:= Cl[T] E).
      etransitivity... apply closure_inc_if. unfold A...
    rewrite HE in HI. intros x Hx.
    apply invim_iff. apply HI...
  - (* 2 -> 0 *)
    intros H V HV. specialize (H (~! V)).
    rewrite <- (compl_compl V), <- invim_compl.
    apply H. do 4 red. rewrite compl_compl...
Qed.

Theorem conti_alt_def: (f :- S ~> T) <->
  (forall x, ForallIn (nbhd[T] (f x)) (fun V =>
    ExistsIn (nbhd[S] x) (fun U => Im f U <:= V) )).
Proof with (auto with sets).
  split.
  - intros H x V (HV1 & HV2). exists (InvIm f V).
    apply H in HV1. apply invim_iff in HV2. split... split...
  - intros H V HV. apply interior_eq_iff.
    apply same_inc_iff. split; try apply interior_in.
    intros x Hx. unfold Interior.
    specialize (H x V (conj HV Hx)) as (Ux & [] & ?).
    exists Ux. split... split... rewrite mkSet_In.
    etransitivity. apply (invim_of_im_inc _ f). apply invim_inc...
Qed.

End MapToEq.


(* Limit and Hausdorff *)
Section TopoStr.
Context {X:Type} `{UsualSetoid X} (T: Topology X).

Definition IsLimit (A: ESet X) (x: X): Prop :=
  ForallIn (nbhd[T] x) (fun U => Inhabited (A //\\ U \\ {{ x }})).
Definition LimitPts (A: ESet X): ESet X :=
  mkSet (IsLimit A).

Theorem closure_limit_rel: forall (A: ESet X),
  Cl[T] A == A \\// LimitPts A.
Proof with (auto with sets).
  intros. apply same_inc_iff. split.
  - (* <:= *)
    intros x HX. decides (x :in: A) as [|K]...
    apply -> closure_nbhd in HX.
    right. intros U HI%HX.
    assert (A //\\ U \\ {{x}} == A //\\ U) as ->...
    rewrite setminus_as_intersect. apply inc_intersect_eq.
    intros y [Hy ?] <-. contradiction.
  - (* =:> *)
    apply union_inc_split. split. apply closure_out.
    intros x Hx. apply closure_nbhd. firstorder.
Qed.
Corollary closed_iff_limit: forall (E: ESet X),
  closed[T] E <-> LimitPts E <:= E.
Proof. intros. rewrite closure_eq_iff, closure_limit_rel. firstorder. Qed.


Definition Converges (a: nat -> X) (x: X): Prop :=
  ForallIn (nbhd[T] x) (fun U => exists N, forall n, n >= N -> a n :in: U).

Definition Hausdorff: Prop :=
  forall x1 x2: X, x1 =/= x2 -> exists (U1 U2: ESet X),
    U1 :in: nbhd[T] x1 /\ U2 :in: nbhd[T] x2 /\ U1 //\\ U2 == EmptySet.


Theorem hausdorff_single_closed: forall x,
  Hausdorff -> closed[T] {{x}}.
Proof with (auto with sets).
  intros x Haus. set (C := Cl[T] {{x}}).
  enough (Claim: C <:= {{x}}).
    apply closure_eq_iff, same_inc_iff. split... apply closure_out.
  intros y Hy. apply -> closure_nbhd in Hy.
  contra. simpl in contra.
  apply Haus in contra as (U1 & U2 & [_ HU1] & (? & <- & HU2)%Hy & EE).
  firstorder.
Qed.

(*
Following requires cardinarlity:
Theorem limit_pt_nbhd_iff: forall A x,
  (forall t, closed[T] {|t|}) ->
  IsLimit A x <-> ForallIn (nbhd[T] x) (fun U => A //\\ U).
Proof.
  
Qed.
*)

Theorem hausdorff_seq_conv_unique: forall (a: nat -> X),
  Hausdorff -> uniqueness (Converges a).
Proof with (auto with arith).
  intros * Haus. unfold uniqueness. intros x y Hx Hy.
  contra.
  apply Haus in contra as (U & V & [N HU]%Hx & [M HV]%Hy & HE).
  apply not_inhabited_empty in HE. apply HE.
  exists (a (N + M)). split...
Qed.

End TopoStr.


Theorem subset_hausdorff: forall X `{UsualSetoid X} T (A: ESet X),
  Hausdorff T -> Hausdorff (SubspaceT T A).
Proof with (auto with sets).
  intros * HT.
  intros x x' Hx. simpl in Hx.
  decides (inclu x = inclu x') as [|K]. exfalso...
  apply HT in K as (U & V & [HU1 HU2] & [HV1 HV2] & HE).
  exists (InvIm inclu U), (InvIm inclu V).
  split; [|split].
  + split... apply im_def...
  + split... apply im_def...
  + rewrite <- invim_intersect, HE...
Qed.


Theorem product_hausdorff: forall X Y `{UsualSetoid X} `{UsualSetoid Y},
  forall (S: Topology X) (T: Topology Y),
  Hausdorff S -> Hausdorff T -> Hausdorff (ProductT S T).
Proof with (auto with sets).
  intros * HS HT. (* HS: Hausdorff S, HT: Hausdorff T *)
  assert (K: prodSubbasis S T <:= opens (ProductT S T)).
    rewrite <- isSubbase_then_generate.
    apply subbase_is_open. apply prod_subbasis_spec.
  intros (x, y) (x', y') Hxy.
  decides (x == x') as [->|Hx]. decides (y == y') as [->|Hy].
  - exfalso...
  - apply HT in Hy as (V & V' & [HV1 HV2] & [HV'1 HV'2] & HE).
    exists (InvIm snd V), (InvIm snd V').
    split; [|split].
    + split... apply K. right. apply im_def...
    + split... apply K. right. apply im_def...
    + rewrite <- invim_intersect. rewrite HE...
  - apply HS in Hx as (U & U' & [HU1 HU2] & [HU'1 HU'2] & HE).
    exists (InvIm fst U), (InvIm fst U').
    split; [|split].
    + split... apply K. left. apply im_def...
    + split... apply K. left. apply im_def...
    + rewrite <- invim_intersect. rewrite HE...
Qed.

