From Practice Require Import Basin.Base.
From Practice Require Import Basin.DecClass.
From Practice Require Import Basin.Sets.
From Practice Require Import Basin.SetLists.
Require Import List.
Import ListNotations.

(* Topology-like structure over type X *)
Record Topolike X (F: Powerset X -> Prop) := mkTopo{
  opens: Powerset X
; topo_proper: properSet opens
; topo_cond: F opens
}.

Arguments mkTopo {X F}.
Arguments opens {X F}.
Arguments topo_proper {X F}.
Arguments topo_cond {X F}.

Property mkTopo_spec: forall X (F: Powerset X -> Prop) (C: Powerset X),
  properSet C -> F C -> exists T: Topolike X F, opens T = C.
Proof. intros * HP HC. exists (mkTopo C HP HC). reflexivity. Qed.

Program Instance setoid_topo X F: Setoid (Topolike X F) := {
  equiv := (fun T T' => opens T == opens T')
}.
Next Obligation. firstorder. Qed.

(* Closed sets: all those where its complement is open *)
Definition closes {X F} (T: Topolike X F): Powerset X :=
  mkSet (fun E => ~! E :in: opens(T)).

(* Open *)
Definition open {X F} (T: Topolike X F): ESet X -> Prop :=
  InSet (opens T).
(* Closed <-> complement is open *)
Definition closed {X F} (T: Topolike X F): ESet X -> Prop :=
  InSet (closes T).


(* Property makeCond_pf {X:Type}: forall (F: Powerset X -> Prop) C,
  properPset C -> F C -> exists S: Conded X F, get S = C.
Proof. intros * HP HB. exists (makeCond _ (conj HP HB)). auto. Qed. *)

Record isTopology {X} (opens: Powerset X): Prop := {
  empty_open: EmptySet :in: opens
; full_open: FullSet :in: opens
; union_open: forall M: Powerset X, M <:= opens -> Unions M :in: opens
; intersect_open: forall U V, U :in: opens -> V :in: opens -> U //\\ V :in: opens
}.
Definition Topology X := Topolike X isTopology.
Arguments empty_open {X} {opens}.
Arguments full_open {X} {opens}.
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

(* Restatements *)
Property empty_is_open: open(T) EmptySet.
Proof. apply empty_open. apply topo_cond. Qed.

Property full_is_open: open(T) FullSet.
Proof. apply full_open. apply topo_cond. Qed.

Property unions_is_open: forall M: Powerset X, ForallIn M (open T) -> open(T) (Unions M).
Proof. apply union_open. apply topo_cond. Qed.

Property intersect_is_open: forall U V: ESet X, open(T) U -> open(T) V -> open(T) (U //\\ V).
Proof. apply intersect_open. apply topo_cond. Qed.

Lemma union_is_open: forall U V: ESet X, open(T) U -> open(T) V -> open(T) (U \\// V).
Proof. intros.
  eapply topo_proper. symmetry. apply unions_couple.
  apply unions_is_open. intros ? [K|K].
  all: eapply topo_proper; [symmetry; apply K | auto].
Qed.

Property proper_opens: properSet (opens(T)).
Proof. apply topo_proper. Qed.


(* Property of closed sets *)
Lemma empty_is_closed: closed(T) EmptySet.
Proof. do 5 red. eapply topo_proper.
  apply empty_compl. apply full_is_open. Qed.

Lemma full_is_closed: closed(T) FullSet.
Proof. do 5 red. eapply topo_proper.
  apply full_compl. apply empty_is_open. Qed.

Lemma intersects_is_closed: forall M: Powerset X,
  ForallIn M (closed(T)) -> closed(T) (Intersects M).
Proof. intros.
  do 5 red. eapply topo_proper.
  rewrite intersects_as_over. apply intersectover_compl.
  apply unions_is_open. intros U [V []].
  eapply topo_proper; eauto. firstorder.
Qed.

Lemma union_is_closed: forall U V: ESet X, closed(T) U -> closed(T) V -> closed(T) (U \\// V).
Proof. intros. do 5 red. eapply topo_proper.
  apply union_compl. apply intersect_is_open; auto. Qed.


Lemma intersect_is_closed: forall U V: ESet X,
  closed(T) U -> closed(T) V -> closed(T) (U //\\ V).
Proof. intros. do 5 red. eapply topo_proper.
  apply intersect_compl. apply union_is_open; auto. Qed.

Lemma proper_closes: properSet (closes(T)).
Proof. intros ? ? ?%compl_mor. unfold closes. apply proper_opens. trivial. Qed.

End Topo.

(* ----------------------------------------------------------------- *)
(*                         Topology Basis                            *)
(* ----------------------------------------------------------------- *)

Record isBase {X} (opens: Powerset X) : Type := {
  bopen_cover: exists (C: Powerset X), C <:= opens /\ cover_all C
; inter_refine_open: forall (U V: ESet X) x,
  U :in: opens -> V :in: opens -> x :in: U //\\ V ->
  exists W, W :in: opens /\ x :in: W /\ (W <:= U //\\ V)
}.
Definition Basis X := Topolike X isBase.
Arguments bopen_cover {X} {opens}.
Arguments inter_refine_open {X} {opens}.

Record isSubbase {X} (opens: Powerset X) : Type := {
  sopen_cover: cover_all opens
}.
Definition Subbasis X := Topolike X isSubbase.
Arguments sopen_cover {X} {opens}.

Section Base.
Context {X:Type}.

(* Obvious lemmas *)
Property topology_is_base (T: Topology X): isBase (opens(T)).
Proof with (auto with sets). split.
  - unfold covers. exists (opens(T)). split... apply unions_inc_one, full_is_open.
  - intros. exists (U //\\ V). split... apply intersect_is_open...
Qed.

Property base_is_subbase (B: Basis X): isSubbase (opens(B)).
Proof. split. pose (bopen_cover(topo_cond B)). firstorder. Qed.

(* Generation *)
Program Definition topoFromBase (B: Powerset X): Powerset X :=
  mkSetWith (fun U => forall x, x :in: U ->
    exists V, V :in: B /\ x :in: V /\ V <:= U) _.
Next Obligation.
  repeat (intros ?; apply DecForall).
  intros ?. apply dec_prop.
Qed.

Property topoFromBase_proper (B: Powerset X): properSet (topoFromBase B).
Proof. do 3 red. intros. unfold topoFromBase. rewrite mkSet_In. rw_refl. Qed.

Lemma base_is_open: forall B, B <:= topoFromBase B.
Proof. intros ? S ? ? ?. exists S. auto with sets. Qed.

Proposition generate_by_base (B: Basis X): isTopology (topoFromBase (opens B)).
Proof with firstorder.
  unfold topoFromBase. split; rewrite mkSet_In.
- (* Empty *) contradiction.
- (* Full *) intros ? ?.
  destruct (bopen_cover(topo_cond B))...
- (* Unions *)
  intros ? H ? [U [I1 I2]]%unions_iff.
  specialize (H _ I1 _ I2) as [V (? & ? & ?)]...
- (* Intersection *)
  intros ? ? HU HV ? [IU IV].
  specialize (HU _ IU) as [S (HU1 & HU2 & HU3)].
  specialize (HV _ IV) as [T (HV1 & HV2 & HV3)].
  destruct (inter_refine_open(topo_cond B) _ _ x HU1 HV1) as [W (H1 & H2 & H3)]...
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
    intros [F (? & E)].
    eapply topoFromBase_proper; eauto. do 4 red in H.
    apply (union_open (generate_by_base B))...
Qed.


Definition baseFromSubbase (S: Powerset X): Powerset X :=
  {' IntersectList L | L in ForallSet S '}.

Lemma subbase_is_base_open: forall S, S <:= baseFromSubbase S.
Proof. intros ? B ?. exists [B]. firstorder. simpl. repeat constructor. auto. Qed.

Proposition generate_by_subbase (S: Subbasis X): isBase (baseFromSubbase (opens S)).
Proof with (auto with sets).
  split.
  - (* Covers *)
    unfold covers. exists (opens S).
    pose (sopen_cover(topo_cond S)). split...
    intros U ?. exists [U].
    unfold ForallSet, IntersectList. split; try symmetry... simpl...
  - (* Intersects *)
    intros ? ? ? [LU (AU & EU)] [LV (AV & EV)] HI.
    exists (U //\\ V). split... apply im_iff.
    exists (LU ++ LV). split; [ apply Forall_app | ]...
    rewrite EU, EV...
Qed.

Program Definition topoByBase (B: Basis X): Topology X := mkTopo (topoFromBase (opens B)) _ _.
Next Obligation. apply topoFromBase_proper. Qed.
Next Obligation. apply generate_by_base. Qed.

Program Definition baseBySubbase (S: Subbasis X): Basis X := mkTopo (baseFromSubbase (opens S)) _ _.
Next Obligation. apply im_proper. Qed.
Next Obligation. apply generate_by_subbase. Qed.

(*  Denotes is that certain powerset serves as a base of the topology *)
Definition isBaseOf (C: Powerset X) (T: Topology X): Prop :=
  exists B: Basis X, opens(B) = C /\ topoByBase B == T.
Definition isSubbaseOf (C: Powerset X) (T: Topology X): Prop :=
  exists S: Subbasis X, opens(S) = C /\ topoByBase (baseBySubbase S) == T.

(* Topology generated by Basis / Subbasis is minimal -> so it is unique *)
Lemma basis_gen_minimal: forall (B: Basis X) (T: Topology X),
  opens(B) <:= opens(T) -> opens(topoByBase B) <:= opens(T).
Proof.
  intros **. unfold topoByBase. simpl.
  rewrite open_iff_base_unions. intros U [F (? & ?)].
  eapply proper_opens; eauto. do 4 red in H0.
  apply unions_is_open. firstorder.
Qed.

Lemma subbasis_gen_minimal: forall (S: Subbasis X) (T: Topology X),
  opens(S) <:= opens(T) -> opens(topoByBase (baseBySubbase S)) <:= opens(T).
Proof.
  intros **. apply basis_gen_minimal.
  unfold baseBySubbase. simpl. intros U [L (H1 & H2)].
  eapply proper_opens; eauto. clear H2.
  induction L as [| V L]; simpl.
  - apply full_is_open.
  - apply intersect_is_open; inversion H1; subst; firstorder.
Qed.

(* TODO Proper set typeclass? *)
Lemma identify_base: forall (T: Topology X) (C: Powerset X),
  properSet C -> C <:= opens(T) ->
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
(*                       Subspace Topology                           *)
(* ----------------------------------------------------------------- *)

(* Subspace topology *)
Section Subspace.
Context {X:Type}.
Context (T: Topology X) (A: ESet X).

Definition subsetOver (C: Powerset X): Powerset (Subset A) :=
  {' InvIm inclu U | U in C '}.

Proposition subspace_topo: isTopology (subsetOver (opens T)).
Proof with (auto with sets; firstorder).
  split; unfold subsetOver.
  - (* Empty *)
    eexists. split; [apply empty_is_open|]...
  - (* Full *)
    eexists. split; [apply full_is_open|]...
  - (* Unions *)
    intros. (* Need W s.t. Unions M == InvIm inclu W *)
    exists (Unions {: U in opens(T) | InvIm inclu U :in: properForm M :}). split.
    + apply unions_is_open. intros ? []...
    + symmetry. rewrite unions_as_over, invim_unionover.
      apply same_inc_iff; split.
      * apply inc_forall_unionover_iff...
      * apply inc_forall_unions_iff. intros V HV.
        specialize (H _ HV) as [U (? & E)]...
  - (* Intersection *)
    intros U U' [V (HV1 & HV2)] [V' (HV'1 & HV'2)].
    exists (V //\\ V'). rewrite invim_intersect.
    split; [apply intersect_is_open | all_rewrite]...
Qed.

Program Definition SubspaceT: Topology (Subset A) := mkTopo (subsetOver (opens T)) _ _.
Next Obligation. apply im_proper. Qed.
Next Obligation. apply subspace_topo. Qed.


Lemma subsp_basis_from_basis: forall C: Powerset X,
  isBaseOf C T -> isBaseOf (subsetOver C) SubspaceT.
Proof.
  intros ? [B (<- & HE)]. do 2 red in HE. apply identify_base.
  - (* Proper *) apply im_proper.
  - (* Contained in subspace topology *)
    unfold opens, SubspaceT, subsetOver.
    apply im_inc. rewrite <- HE. apply base_is_open.
  - (* Forms basis of the topo *)
    intros V [U (HU%HE & EV)] y Hy%EV.
    specialize (HU (inclu y) Hy) as [W (? & ? & ?)].
    exists (InvIm inclu W). firstorder.
Qed.

Section UsualEq.
Context `{UsualEqDec X}.

Lemma open_subsp_open_whole: forall U: ESet (Subset A),
  open(T) A -> open(SubspaceT) U -> open(T) (Im inclu U).
Proof with (eauto with sets).
  intros * ? [V [? E]]%im_iff.
  assert (Im inclu U == A //\\ V); [rewrite E|]...
  eapply proper_opens... apply intersect_is_open...
Qed.

Lemma closed_subsp_iff: forall E: ESet (Subset A),
  ExistsIn (closes(T)) (fun F => InvIm inclu F == E) <-> closed(SubspaceT) E.
Proof with (eauto with sets). intros *. split.
  - (* -> *)
    intros [F [HC HE]]. do 4 red in HC.
    do 5 red. firstorder.
  - (* <- *)
    intros [U [HO HE]]. exists (~! U). split.
    do 4 red. eapply proper_opens...
    rewrite <- invim_compl, <- HE...
Qed.
Corollary closed_subsp_def: forall F: ESet X,
  closed(T) F -> closed(SubspaceT) (InvIm inclu F).
Proof. intros **. apply closed_subsp_iff.
  exists F. split; auto with sets. Qed.

Lemma closed_subsp_closed_whole: forall (E: ESet (Subset A)),
  closed(T) A -> closed(SubspaceT) E -> closed(T) (Im inclu E).
Proof with (eauto with sets).
  intros * HA [V []]%invim_iff.
  assert (E == InvIm inclu (~! V)).
    rewrite <- invim_compl, <- H1...
  assert (Im inclu E == A //\\ ~! V).
    rewrite H2...
  eapply proper_closes... apply intersect_is_closed...
  eapply proper_opens...
Qed.

End UsualEq.

End Subspace.

(* ----------------------------------------------------------------- *)
(*                        Product Topology                           *)
(* ----------------------------------------------------------------- *)

Section Product.
Context {X Y:Type}.
Context (S: Topology X) (T: Topology Y).

Definition prodOver (C: Powerset X) (D: Powerset Y): Powerset (X * Y) :=
  {' U ** V | '(U, V) in C ** D '}.

Proposition prod_basis: isBase (prodOver (opens S) (opens T)).
Proof with (eauto 4 with sets).
  split; unfold prodOver.
  - (* Covers *)
    exists {| FullSet |}. split.
    + intros W ?%singleton_iff. eexists. split.
      apply prod_iff. split; apply full_is_open.
      etransitivity...
    + red...
  - (* Intersection *)
    intros W1 W2 x [(U1, V1) [H1 E1]] [(U2, V2) [H2 E2]] H.
    exists (W1 //\\ W2). split...
    apply prod_iff in H1 as (HU1 & HV1). apply prod_iff in H2 as (HU2 & HV2).
    specialize (intersect_is_open _ _ _ HU1 HU2) as H1.
    specialize (intersect_is_open _ _ _ HV1 HV2) as H2.
    eexists. split. apply prod_iff. split... all_rewrite...
Qed.

Program Definition ProductB: Basis (X * Y) := mkTopo (prodOver (opens S) (opens T)) _ _.
Next Obligation. apply im_proper. Qed.
Next Obligation. apply prod_basis. Qed.

Definition ProductT: Topology (X * Y) := topoByBase ProductB.


Lemma prod_basis_from_basis: forall (B: Powerset X) (C: Powerset Y),
  isBaseOf B S -> isBaseOf C T ->
  isBaseOf (prodOver B C) ProductT.
Proof with (eauto with sets).
  intros * [Bt (? & EB)] [Ct (? & EC)]; subst.
  apply identify_base.
  - apply im_proper.
  - (* Contained in ProductT *)
    etransitivity; [| apply base_is_open].
    intros P [(U, V) (? & ?)]. exists (U, V).
    firstorder.
  - (* Forms basis of the topo *)
    intros W HW (x, y) Hxy.
    specialize (HW (x, y) Hxy) as [P [[(U, V) (HI & HE)] (HR1 & HR2)]].
    rewrite HE in *.
    destruct HI as (HU%EB & HV%EC). destruct HR1 as (HU2 & HV2).
    specialize (HU x HU2) as [I (?&?&?)]. specialize (HV y HV2) as [J (?&?&?)].
    exists (I ** J). split. eexists (_, _)...
    split... etransitivity; eauto...
Qed.


Definition prodSubbasis: Powerset (X * Y) :=
  {' InvIm fst U | U in opens S '} \\// {' InvIm snd V | V in opens T '}.

Theorem prod_subbasis_spec:
  isSubbaseOf prodSubbasis ProductT.
Proof with (eauto with sets).
  destruct (mkTopo_spec _ isSubbase prodSubbasis) as [B HS].
  - (* Proper *)
    unfold prodSubbasis. apply proper_union; apply im_proper.
  - (* Subbase (cover) *)
    split. unfold covers. apply unions_inc_one.
    left. eexists. split; [apply full_is_open|]...
  - (* Generates exact *)
    exists B. split; auto. apply same_inc_iff. split.
    + (* open ProductT =:> *)
      apply subbasis_gen_minimal.
      etransitivity; [| apply base_is_open]. rewrite HS.
      apply union_inc_split. split.
      all: intros ? [? []]; eapply im_proper...
      all: eexists (_, _); split...
      all: split; auto; apply full_is_open.
    + (* open ProductT <:= *)
      apply basis_gen_minimal. etransitivity; [| apply base_is_open].
      intros P [(U, V) ((HU & HV) & HP)]. apply im_iff.
      exists [InvIm fst U; InvIm snd V]. rewrite HS. split.
      * repeat apply Forall_cons; [left | right | constructor].
        all: apply im_def...
      * rewrite IntersectList_couple. etransitivity...
Qed.

End Product.

(* The theorem below requires mapping topology over bijective map
Theorem prod_subsp_exch: forall X Y (S: Topology X) (T: Topology Y),
  forall (A: ESet X) (B: ESet Y),
  open (ProductT (SubspaceT S A) (SubspaceT T B)) '= open (SubspaceT (ProductT S T) (A ** B)).
*)


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

Property interior_eq_iff: forall A, open(T) A <-> Interior A == A.
Proof with eauto.
  firstorder. eapply proper_opens...
  apply unions_is_open. firstorder. Qed.

Property closure_eq_iff: forall A, closed(T) A <-> Closure A == A.
Proof with eauto.
  firstorder. eapply proper_closes...
  apply intersects_is_closed. firstorder. Qed.

Property interior_open: forall A, open(T) (Interior A).
Proof. intros. apply unions_is_open. firstorder. Qed.

Property closure_closed: forall A, closed(T) (Closure A).
Proof. intros. apply intersects_is_closed. firstorder. Qed.

End TopoStr.

Lemma subspace_closure: forall X `(UsualEqDec X) T (Y: ESet X) (A: ESet (Subset Y)),
  let S := SubspaceT T Y in
  Closure(S) A == InvIm inclu (Closure(T) (Im inclu A)).
Proof with (auto with sets).
  intros. apply same_inc_iff. split.
  - (* Cl(S) A <:= Cl A /\ Y *)
    set (E := Closure T (Im inclu A)).
    apply intersects_inced_one. split.
    apply closed_subsp_def with (F := E)... apply closure_closed.
    do 3 red. rewrite <- (incl_invim_of_im A).
    apply invim_inc. apply closure_out.
  - (* Cl(S) A =:> Cl A /\ Y *)
    set (B := Closure(S) A).
    assert (closed(S) B) as [C (? & HE)]%closed_subsp_iff by apply closure_closed...
    rewrite <- HE. apply invim_inc, intersects_inced_one.
    split... do 3 red. transitivity (Y //\\ C)...
    rewrite <- incl_im_of_invim. apply im_inc.
    rewrite HE. apply closure_out.
Qed.


Lemma closure_intersects: forall X T (A: ESet X) x,
  x :in: Closure(T) A <-> ForallIn (opens(T)) (fun U => x :in: U -> Inhabited (A //\\ U)).
Proof with (auto with sets).
  split.
  - (* -> *)
    intros H U H1 H2. decides (Inhabited (A //\\ U)) as [K|K]...
    exfalso. apply not_inhabited_empty in K.
    assert (I: A <:= ~! U). firstorder.
    specialize (H (~! U)). apply H...
    split... eapply proper_opens; [|eauto]...
  - (* <- *)
    intros H E [HC HI]. decides (x :in: E) as [K|K]...
    exfalso. specialize (H (~!E) HC K) as [?]. firstorder.
Qed.
Corollary closure_intersects_basis: forall X S (A: ESet X) x,
  let T := topoByBase S in
  x :in: Closure(T) A <-> ForallIn (opens(S)) (fun B => x :in: B -> Inhabited (A //\\ B)).
Proof with (auto with sets).
  intros. etransitivity. apply closure_intersects. split.
  - intros H B ? ?. apply H... apply base_is_open...
  - intros H U HO [V (? & ? & ?)]%HO. firstorder.
Qed.


Definition Neighborhood {X} (T: Topology X) x: Powerset X :=
  {: U in opens(T) | x :in: U :}.

Corollary closure_nbhd: forall X T (A: ESet X) x,
  x :in: Closure(T) A <-> ForallIn (Neighborhood(T) x) (fun U => Inhabited (A //\\ U)).
Proof. intros. etransitivity. apply closure_intersects. firstorder. Qed.


Section TopoStr.
Context {X:Type} `{UsualEqDec X} (T: Topology X).

Definition IsLimit (A: ESet X) (x: X): Prop :=
  ForallIn (Neighborhood(T) x) (fun U => Inhabited (A //\\ U \\ {| x |})).
Definition LimitPts (A: ESet X): ESet X :=
  mkSetWith (IsLimit A) (fun _ => decide _).

Theorem closure_limit_rel: forall (A: ESet X),
  Closure(T) A == A \\// LimitPts A.
Proof with (auto with sets).
  intros. apply same_inc_iff. split.
  - (* <:= *)
    intros x HX. decides (x :in: A) as [K|K]...
    apply -> closure_nbhd in HX.
    right. intros U HI%HX.
    assert (A //\\ U \\ {|x|} == A //\\ U) as ->...
    rewrite setminus_as_intersect. apply inc_intersect_eq.
    intros y [Hy ?]. rewrite compl_iff, singleton_iff. intros ->...
  - (* =:> *)
    apply union_inc_split. split. apply closure_out.
    intros x Hx. apply closure_nbhd. firstorder.
Qed.
Corollary closed_iff_limit: forall (E: ESet X),
  closed(T) E <-> LimitPts E <:= E.
Proof. intros. rewrite closure_eq_iff, closure_limit_rel. firstorder. Qed.


Definition Converges (a: nat -> X) (x: X): Prop :=
  ForallIn (Neighborhood(T) x) (fun U => exists N, forall n, n >= N -> a n :in: U).

Definition Hausdorff: Prop :=
  forall x1 x2: X, x1 =/= x2 -> exists (U1 U2: ESet X),
    U1 :in: Neighborhood(T) x1 /\ U2 :in: Neighborhood(T) x2 /\ U1 //\\ U2 == EmptySet.


Theorem hausdorff_single_closed: forall x,
  Hausdorff -> closed(T) {|x|}.
Proof with (auto with sets).
  intros x Haus. set (C := Closure(T) {|x|}).
  assert (Claim: C <:= {|x|}). {
    intros y Hy%closure_nbhd. decides (x == y) as [E|E]...
    apply Haus in E as (U1 & U2 & [? HU1%unwrap_mkin] & (? & <- & HU2)%Hy & EE).
    firstorder. }
  apply closure_eq_iff. apply same_inc_iff. split... apply closure_out.
Qed.

(*
Following requires cardinarlity:
Theorem limit_pt_nbhd_iff: forall A x,
  (forall t, closed(T) {|t|}) ->
  IsLimit A x <-> ForallIn (Neighborhood x) (fun U => A //\\ U).
Proof.
  
Qed.
*)

Theorem hausdorff_seq_conv_unique: forall (a: nat -> X),
  Hausdorff -> uniqueness (Converges a).
Proof with auto.
  intros * Haus. unfold uniqueness. intros x y Hx Hy.
  decides (x == y) as [E|E]... exfalso.
  apply Haus in E as (U & V & [N HU]%Hx & [M HV]%Hy & HE).
  apply not_inhabited_empty in HE. apply HE.
  exists (a (N + M)). split; auto with arith.
Qed.

End TopoStr.


Theorem subset_hausdorff: forall X `{UsualEqDec X} T (A: ESet X),
  Hausdorff T -> Hausdorff (SubspaceT T A).
Proof with (auto with sets).
  intros * HT.
  intros x x' Hx. simpl in Hx.
  decides (inclu x == inclu x') as [|K]. exfalso...
  apply HT in K as (U & V & [HU1 HU2] & [HV1 HV2] & HE).
  exists (InvIm inclu U), (InvIm inclu V).
  split; [|split].
  + split... apply im_def...
  + split... apply im_def...
  + rewrite <- invim_intersect, HE...
Qed.


Theorem product_hausdorff: forall X Y `{UsualEqDec X} `{UsualEqDec Y},
  forall (S: Topology X) (T: Topology Y),
  Hausdorff S -> Hausdorff T -> Hausdorff (ProductT S T).
Proof with (auto with sets).
  intros * HS HT.
  assert (K: prodSubbasis S T <:= opens (ProductT S T)).
    destruct (prod_subbasis_spec S T) as (B & HB1 & HB2).
    do 2 red in HB2. rewrite <- HB1, <- HB2.
    etransitivity. apply subbase_is_base_open. apply base_is_open.
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


(* ----------------------------------------------------------------- *)
(*                       Continuous Functions                        *)
(* ----------------------------------------------------------------- *)

Definition Continuous {X Y} (S: Topology X) (T: Topology Y) (f: X -> Y): Prop :=
  ForallIn (opens(T)) (fun V => open(S) (InvIm f V)).

Lemma basis_invim_conti: forall X Y (S: Topology X) (B: Basis Y) (f: X -> Y),
  ForallIn (opens(B)) (fun V => open(S) (InvIm f V)) -> Continuous S (topoByBase B) f.
Proof.
  intros ** V (F & HV1 & HV2)%open_iff_base_unions.
  assert (E: InvIm f V == unions W in F, InvIm f W).
    rewrite <- invim_unionover, <- unions_as_over. rw_refl.
  eapply proper_opens; eauto. clear E.
  apply unions_is_open. intros U (W & HW1 & HW2).
  eapply proper_opens; eauto. firstorder.
Qed.



Definition Foo := 0.



