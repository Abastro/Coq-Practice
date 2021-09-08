(* ----------------------------------------------------------------- *)
(*                      Basic Category Theory                        *)
(* ----------------------------------------------------------------- *)

From Practice Require Import Base Graph.
From mathcomp Require Export tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.


(* ----------------------------------------------------------------- *)
(*                     Insignificant Morphism                        *)
(* ----------------------------------------------------------------- *)




(* Module NatSort := Sort NatB. *)

Module Type HasSCat (Import T: Equalities.Typ).
Parameter R: t -> t -> Prop.
Axiom PO: PreOrder R.
Existing Instance PO.
End HasSCat.
Module Type SCat := Equalities.Typ <+ HasSCat.


Module SDiag (Import M: SCat).

Definition U := M.t.

(* Convenient way to make a graph *)
Definition MkGraph n (t: seq (nat * nat)): graph n :=
  relgraph [rel i j | (nat_of_ord i, nat_of_ord j) \in t].


Section Env1.
Variable n: nat.
Variable V: n.-tuple U.

Definition hold (G: graph n) :=
  forall a b, (grrel G: rel _) a b -> R (tnth V a) (tnth V b).

Lemma hold_trans G: hold G -> hold (transCl G).
Proof.
  move=> H x y. move/transClP=> [p + ->].
  elim: p x=> [| z p' IH] /= x.
  - reflexivity.
  - move/andP=> [Hr /IH]. apply: transitivity. by apply /H.
Qed.

Lemma hold_incl (G K: graph n): grincl G K -> hold K -> hold G.
Proof. move/grincl_rel=> + + x y. move=> /(_ x y) + /(_ x y). firstorder. Qed.

Lemma hold_add (G K: graph n): hold G -> hold K -> hold (gradd G K).
Proof. move=> HG HK a b. rewrite graddK=> /orP [/HG|/HK] //. Qed.

End Env1.


Section Env2.
Variable m n: nat.
Variable W: n.-tuple U.
Variable f: 'I_m -> 'I_n.

Lemma hold_embed G: hold (tupleOf (tnth W \o f)) G -> hold W (graphim f G).
Proof.
  move=> H a' b' /=.
  rewrite tupleOf_tnth filter_enumOrd_enum.
  move=> /flatten_mapP[a].
  rewrite mem_enum=> /eqP <-.
  move=> /mapP[b] Hab ->.
  move: (H _ _ Hab). by rewrite !tupleOf_tnth.
Qed.

Lemma hold_embed_eq G V:
  val V = val (tupleOf (tnth W \o f)) -> hold V G -> hold W (graphim f G).
Proof. move=> /val_inj ->. apply/hold_embed. Qed.

Lemma hold_preim G: hold W G -> hold (tupleOf (tnth W \o f)) (graphpre f G).
Proof.
  move=> H a b /=.
  rewrite !tupleOf_tnth filter_enumOrd_enum mem_enum.
  by move/H.
Qed.

End Env2.


(*
  Finds a value x in sequence l with "y = f x" by computation.
  The result is wrapped in phantom.
*)
Ltac findIn f l y :=
  match eval compute in l with
  | ?x :: ?l' =>
    lazymatch eval compute in (f x) with
    | y => move: (Phantom _ x)
    | _ => findIn f l' y
    end
  end.

(*
  Remove duplicates in the list.
  The result is wrapped in phantom.
*)
Ltac rmdup l :=
  lazymatch type of l with
  | seq ?U =>
    let ids := eval simpl in (fun x: U => x) in
    match eval compute in l with
    | [::] => move: (Phantom (seq U) [::])
    | ?a :: ?l' =>
      rmdup l';
      match goal with [ |- phantom _ ?res -> _ ] =>
        move=> _;
        tryif (findIn ids res a)
        then move=> _; move: (Phantom (seq U) res)
        else move: (Phantom (seq U) (a :: res))
      end
    end
  | _ => fail 0 "type of " l " isn't a seq"
  end.


(*
  Finds a mapping "f: 'I_m -> 'I_n" where
  "v =1 w \o f" under simplification.
  The result is wrapped in phantom and discharged into the goal.
*)
Ltac findMap v w :=
  lazymatch type of v with
  | 'I_?m -> ?T =>
    lazymatch type of w with
    | 'I_?n -> ?T =>
      (* list of b s.t. w b = v a for each element a in l *)
      let rec findAll l :=
        lazymatch eval compute in l with
        | [::] => move: (Phantom (seq 'I_n) [::])
        | ?a :: ?l' =>
          let y := eval compute in (v a) in
          findAll l';
          findIn w (enumOrd n) y || fail 0 "cannot find " y " from result of " w;
          match goal with [ |- phantom _ ?b -> phantom _ ?t -> _ ] =>
            move=> _ _;
            move: (Phantom (seq 'I_n) (b :: t))
          end
        end
      in
      findAll (enumOrd m);
      match goal with [ |- phantom _ ?res -> _ ] =>
        move => _;
        move: (Phantom ('I_m -> 'I_n) (tnth [tuple of res]))
      end
    | _ => fail 0 "type of " w " is not 'I_?n -> T"
    end
  | _ => fail 0 "type of " v " is not 'I_?m -> ?T"
  end.

(* Simplifies the top hold. Use this to view how it is currently *)
Ltac holdSimpl := lazymatch goal with
  | [ |- hold _ ?G -> _ ] => 
    let vG := eval compute in (val G) in
    have ->: G = [tuple of vG] by apply/val_inj
  | _ => fail 0 "Top assumption should be 'hold'"
  end.

(* Apply image to the top hold *)
Ltac holdTo W := lazymatch goal with
  | [ |- hold ?V _ -> _ ] =>
    findMap (tnth V) (tnth W);
    lazymatch goal with [ |- phantom _ ?f -> _ ] =>
      move=> _ /(hold_embed_eq (W := W) (f := f))=> /(_ erefl)
    end
  | _ => fail 0 "Top assumption should be 'hold'"
  end.

(* Adds two top hold statements, applying transitive closure *)
Ltac holdAdd := lazymatch goal with
  | [ |- hold ?V ?G -> hold ?W ?K -> _ ] =>
    rmdup (V ++ W);
    match goal with [ |- phantom _ ?e -> _ ] =>
      move=> _;
      let n := fresh "N" in
      let E := eval simpl in [tuple of e] in
      holdTo E => n;
      holdTo E;
      move=> /(hold_add n) /hold_trans {n}
    end
  | _ => fail 0 "Top 2 assumptions should be 'hold'"
  end.


Local Example ex_hold_move: forall (a b c d: U),
  hold [tuple a; b] (MkGraph _ [:: (0, 1)]) ->
  hold [tuple b; c] (MkGraph _ [:: (0, 1)]) ->
  hold [tuple a; c; b; d] (MkGraph _ [:: (0, 1); (2, 1)]).
Proof.
  move=> a b c d.
  holdAdd. holdTo [tuple a; c; b; d].
  by apply/hold_incl.
Qed.

End SDiag.


(*
(* Simple labeled diagram with insignificant morphisms *)
Module SDiag (Import M: SCat).

Definition U := M.t.

(* A diagram holds iff arrows from current node holds and remaining subdiagram holds *)
Inductive Hold (d: U): list U -> DAG.t -> Prop :=
  | Hold_nil: Hold d [] []
  | Hold_cons: forall a e l G, Forall (fun n => R a (rth n l d)) e ->
    Hold d l G -> Hold d (a :: l) (e :: G)
.

Property Hold_inv: forall d a e l G,
  Hold d (a :: l) (e :: G) -> Forall (fun n => R a (rth n l d)) e /\ Hold d l G.
Proof. move=> d a e l G H. inversion H; subst. done. Qed.

Property hold_len: forall d l G, Hold d l G -> length l = length G.
Proof. move=> d l G. elim=> //= a e {}l {}G Hh Ht IH. by f_equal. Qed.


(* TODO simplify *)
Property hold_edge: forall d l G, DAG.DAGF G ->
  Hold d l G <-> length l = length G /\
  forall m n, DAG.hasEdge G m n -> R (rth m l d) (rth n l d).
Proof with eauto.
  move=> d l G DAGF. split.
  - (* -> *)
    move=> H. split. apply: hold_len... move=> m n HasE.
    have {}DAGF : n < m < length G.
    { split. apply: DAG.DAG_edge... apply: DAG.hasEdge_valid... }

    elim: H HasE DAGF=> [| a e l' G' Hh Ht IH] /=. lia.
    move=> HasE Lnm. have Lm: m <= length G' by lia.
    rewrite /DAG.hasEdge in HasE. have {}Ht := (hold_len Ht).

    case: (Lt.le_lt_or_eq _ _ Lm) HasE=> {Lm} [Lm|->].
    + rewrite /DAG.edge !rth_tl //; try lia. move=> ?. apply: IH=> //. lia.
    + rewrite /DAG.edge -{2}Ht !rth_hd rth_tl => {IH}. lia. move=> {Lnm}.
      move: n. by apply /Forall_forall.

  - (* <- *)
    move=> [Len H].
    elim: DAGF l Len H=> [| e G' Hh Ht IH] [| a l'] //=. constructor.
    move=> [Len] H.  have {}IH := (IH _ Len).

    constructor.
    + apply/Forall_forall=> n Hn. move: (H (length l') n).
      rewrite rth_hd /DAG.hasEdge /DAG.edge Len rth_hd=> /(_ Hn).
      rewrite rth_tl // Len. move: n Hn.
      by apply /Forall_forall /(Sorted_extends trans_gt).
    + apply: IH=> m n HasE. move: (H m n).
      have Lm := (DAG.hasEdge_valid HasE).
      have Ln := (DAG.DAG_edge Ht HasE).
      rewrite /DAG.hasEdge /DAG.edge !rth_tl; try lia.
      move=> /(_ HasE) //.
Qed.

Lemma hold_incl: forall d l G K,
  DAG.DAGF G -> DAG.DAGF K -> DAG.Incl G K -> Hold d l K -> Hold d l G.
Proof.
  move=> d l G K HG HK HI. rewrite !hold_edge //.
  have Len := Forall2_len HI. have {}HI := DAG.Incl_edge HI.
  firstorder. lia.
Qed.

(*
Lemma hold_add_empty: forall d l G N, Hold d l G -> Hold d l (repeat [] N ++ G).
Proof. move=> d l G + H. elim=> //= N' IH. constructor=> //. by apply: IH. Qed.
*)


Proposition hold_transCl: forall d l G,
  Hold d l G -> Hold d l (DAG.transClosure G).
Proof.
  move=> d l G. elim=> [| a e l' G' Hh Ht IH] /=; constructor=> //.
  apply /Forall_forall=> n.
  move=> /filter_In []. rewrite -in_rev => /in_seq [_ /= Ln].
  move=> /existsb_exists [s [Hs]].

  move/orP=> [/Nat.eqb_spec -> | /NatB.InP Hn].
  - move: s Hs. by apply /Forall_forall.
  - move: M.Tr=> Tr. transitivity (rth s l' d).
    + move=> {Hn}. move: s Hs. by apply /Forall_forall.
    + move: IH. rewrite hold_edge. move=> [_ +]. by apply. apply: DAG.transCl_DAG.
Qed.

Proposition hold_extend: forall d L tar N l G,
  Sorted gt (N :: tar) -> length tar = length G ->
  l = map (fun m => rth m L d) tar ->
  DAG.DAGF G -> Hold d l G -> Hold d L (DAG.extend N tar G).
Proof.
  move=> d L tar + _ G + + ->.
  elim: tar G=> [|n tar' IH] [|e G'] N //. {
    admit.
    (*
    rewrite /= -(app_nil_r (repeat [] N)) => _ _ _ _.
    apply: hold_add_empty. constructor.
    *)
  }
  
  move=> OrdT. move: (Sorted_inv OrdT)=> [{}OrdT /HdRel_iff Ln].
  move=> [EqL] DAGF.
  have OrdE := Memoized_inv DAGF. have {}DAGF := Memoized_inv_tail DAGF.
  have {}IH := (IH _ _ OrdT EqL DAGF). move=> {DAGF}.

  move=> /= /Hold_inv [Hh Ht].

  (* Conditioning on L.. *)

  simpl. apply: hold_add_empty. constructor.
  - rewrite DAG.extend_len //.
    apply /Forall_forall=> _ /in_map_iff [+ [<-]]. apply /Forall_forall.
    move: OrdE=> /Sorted_inv_Forall [+ _].
    move/(Forall_and Hh). apply: Forall_impl=> m [+ Lm].
    congr R.
    + rewrite /= rth_hd2 // map_length //.
    + pose f s := rth s L d.
      rewrite -/f (rth_indep _ (f 0)). rewrite map_length /=. lia.
      rewrite map_rth //.
  - apply: IH. admit.
Admitted.

End SDiag.
*)




