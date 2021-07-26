Require Import PeanoNat.
Require Import Bool.
Require Import List.
Require Import Basics.

Require Import ssrfun.
Require Import Lia.

Module PigeonholePrinciple.
(* Denotes repetition *)
Fixpoint Repeats {X:Type} (l: list X) : Prop :=
  match l with
  | nil => False
  | x :: l' => In x l' \/ Repeats l'
  end.

Lemma repeat_map: forall X Y (f: X->Y) (l: list X),
  Repeats l -> Repeats (map f l).
Proof.
  intros. induction l; try contradiction.
  simpl in *. destruct H.
  - left. apply in_map. apply H.
  - right. tauto.
Qed.

Lemma repeat_injection: forall X Y (f: X->Y) (l: list X),
  injective f -> Repeats (map f l) -> Repeats l.
Proof.
  intros X Y f l INJ H. induction l; try contradiction.
  simpl in *. destruct H.
  - left. apply in_map_iff in H as [x [E H]]. apply INJ in E. subst. assumption.
  - right. tauto.
Qed.

Lemma repeat_insert: forall X (x: X) (l1 l2: list X),
  In x (l1 ++ l2) \/ Repeats (l1 ++ l2) -> Repeats (l1 ++ x :: l2).
Proof with (auto with datatypes).
  intros X x l1 l2 [H | H].
  - (* In x (l1 ++ l2) *)
    induction l1 as [| s l1' IH]; simpl in *...
    destruct H; subst; simpl...
  - (* Repeats (l1 ++ l2) *)
    induction l1 as [| s l1' IH]; simpl in *...
    destruct H... rewrite in_app_iff in H. destruct H...
Qed.

(* Creates the list of positions marking the indices *)
Lemma mk_index_list: forall (X:Type) (l1 l2: list X),
  incl l1 l2 -> exists ln: list nat, map (nth_error l2) ln = map Some l1.
Proof with auto.
  intros. induction l1. { exists nil... }
  apply incl_cons_inv in H as [H1 H2].
  apply In_nth_error in H1 as [n H].
  apply IHl1 in H2 as [ln H2]. exists (n :: ln).
  simpl. f_equal...
Qed.

Theorem pigeonhole_nat:
  forall (l : list nat), length l > 0 ->
  Forall (fun n => S n < length l) l -> Repeats l.
Proof with (auto with datatypes).
  assert (WTS: forall N,
    forall (l : list nat), S N = length l ->
    Forall (fun n => S n < S N) l -> Repeats l). {
    induction N as [| N' IH]; intros l HL H. {
      (* Length 1 *)
      destruct l; simpl in *; try apply Forall_inv in H; try lia.
    } (* Otherwise *)

    (* Recursive Step *)
    assert (REC: forall m l1 l2, l = l1 ++ m :: l2 -> ~In N' (l1 ++ l2) -> Repeats l). {
      intros m l1 l2 HA NC. subst. apply repeat_insert. right.
      apply IH. { rewrite app_length in *. simpl in *. lia. }
      apply incl_Forall with (l2 := l1 ++ l2) in H...
      apply Forall_impl with (P := fun n => S n < S (S N') /\ n <> N'); try lia.
      apply Forall_and...
      rewrite Forall_forall; unfold not; intros; subst; contradiction.
    }

    destruct (in_dec Nat.eq_dec N' l) as [HC | HNC].
    - (* contains *)
      apply in_split in HC as [l1 [l2 HC]]. subst.
      destruct (in_dec Nat.eq_dec N' (l1 ++ l2)) as [HC' | HNC'].
      + apply repeat_insert... (* contains 2+ *)
      + apply (REC N' l1 l2)... (* contains 1 *)
    - (* not contains *)
      destruct l as [| n l']; simpl in *; try lia. apply (REC n nil l')...
  }
  intros l HL H. destruct (length l) as [| N] eqn:E; try lia.
  apply WTS with N...
Qed.

Theorem pigeonhole_principle:
  forall (X:Type) (l1 l2:list X),
  incl l1 l2 -> length l2 < length l1 -> Repeats l1.
Proof with (auto with datatypes).
  intros X l1 l2 H HL.
  apply mk_index_list in H as [ln H].
  apply repeat_injection with (f := Some).
  { unfold injective. intros. injection H0... }
  rewrite <- (map_length Some l1) in HL. rewrite <- H in *.
  apply repeat_map. rewrite map_length in *.
  apply pigeonhole_nat; try lia.

  apply Forall_impl with (fun n => nth_error l2 n <> None).
  - clear H. intros n H. unfold lt. apply nth_error_Some in H.
    transitivity (S (length l2)); lia.
  - clear HL. apply Forall_forall. intros n HI.
    apply in_map with (f := nth_error l2) in HI. rewrite H in HI.
    apply in_map_iff in HI as [x [P _]]. rewrite <- P. discriminate.
Qed.

(* Note: Repeat has duplicates - may require decidable equality *)
Theorem repeat_then_dup: forall X (l: list X), Repeats l -> ~ NoDup l.
Proof with (auto with datatypes).
  intros. induction l... unfold not. intros HD. inversion HD; subst.
  simpl in H. tauto.
Qed.

End PigeonholePrinciple.

