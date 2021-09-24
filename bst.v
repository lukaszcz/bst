(* Binary search trees *)
(* Requires CoqHammer >= 1.3 *)

From Hammer Require Import Tactics Reflect.

Require Import Sorting.Permutation.

Require List.
Open Scope list_scope.
Import List.ListNotations.

Class DecTotalOrder (A : Type) := {
  leb : A -> A -> bool;
  leb_total : forall x y, leb x y \/ leb y x;
  leb_antisym : forall x y, leb x y -> leb y x -> x = y;
  leb_trans : forall x y z, leb x y -> leb y z -> leb x z }.

Instance dto_nat : DecTotalOrder nat.
Proof.
  apply Build_DecTotalOrder with (leb := Nat.leb);
    induction x; sauto.
Defined.

Lemma leb_refl `{DecTotalOrder} : forall x, leb x x.
Proof.
  intro x; destruct (leb_total x x); auto.
Qed.

Definition leb_total_dec `{DecTotalOrder}
  : forall x y, {leb x y}+{leb y x}.
  intros x y.
  sdestruct (leb x y).
  - left; constructor.
  - right; destruct (leb_total x y); auto.
Defined.

Definition eq_dec {A} `{DecTotalOrder A} : forall x y : A, {x = y}+{x <> y}.
  intros x y.
  sdestruct (leb x y).
  - sdestruct (leb y x).
    + auto using leb_antisym.
    + sauto.
  - sdestruct (leb y x).
    + sauto.
    + destruct (leb_total_dec x y); auto.
Defined.

Definition eqb `{DecTotalOrder} x y : bool :=
  if eq_dec x y then
    true
  else
    false.

Definition ltb `{DecTotalOrder} x y : bool :=
  leb x y && negb (eqb x y).

Definition leb_ltb_dec `{DecTotalOrder} x y : {leb x y}+{ltb y x}.
  destruct (leb_total_dec x y).
  - left; sauto.
  - unfold ltb, negb, eqb.
    destruct (eq_dec y x).
    + left; sauto.
    + right; sauto b: on.
Defined.

Lemma lem_ltb_to_leb `{DecTotalOrder} :
  forall x y : A, ltb x y -> leb x y.
Proof.
  sauto b: on unfold: ltb.
Qed.

Lemma lem_ltb_spec `{DecTotalOrder} :
  forall x y, ltb x y <-> leb x y /\ x <> y.
Proof.
  hauto lqb: on unfold: ltb, eqb.
Qed.

Lemma lem_eqb_spec `{DecTotalOrder} :
  forall x y, eqb x y <-> x = y.
Proof.
  hauto lq: on rew: off unfold!: eqb.
Qed.

Lemma lem_ltb_not_leb `{DecTotalOrder} :
  forall x y : A, ltb x y <-> ~ leb y x.
Proof.
  split.
  - sauto use: lem_ltb_spec.
  - destruct (leb_total_dec x y);
      qauto use: lem_ltb_spec.
Qed.

(*********************************************************************)

Inductive tree A := empty | node (x : A) (l r : tree A).

Arguments empty {A}.
Arguments node {A}.

Inductive All {A} (P : A -> Prop) : tree A -> Prop :=
| All_empty : All P empty
| All_node : forall x l r, P x -> All P l -> All P r -> All P (node x l r).

Inductive BST `{DecTotalOrder} : tree A -> Prop :=
| BST_empty : BST empty
| BST_node : forall x l r, All (fun y => leb y x) l -> All (ltb x) r ->
                           BST l -> BST r -> BST (node x l r).

Lemma lem_all_trans {A} (P Q : A -> Prop) :
  forall t, All P t -> (forall x, P x -> Q x) -> All Q t.
Proof.
  induction 1; sauto.
Qed.

Lemma lem_all_ltb_trans `{DecTotalOrder} :
  forall x x' t, All (ltb x) t -> leb x' x ->
                 All (ltb x') t.
Proof.
  hauto lq: on use: lem_all_trans, lem_ltb_not_leb, leb_trans.
Qed.

Lemma lem_all_leb_ltb_eq `{DecTotalOrder} :
  forall x x' t, All (fun y => leb y x) t -> ltb x x' ->
                 All (fun y => x' <> y) t.
Proof.
  induction 1; sauto lq: on rew: off use: lem_ltb_spec, leb_antisym.
Qed.

(*********************************************************************)
(* elements *)

Fixpoint elements {A} (t : tree A) : list A :=
  match t with
  | empty => []
  | node x l r => elements l ++ x :: elements r
  end.

Inductive Sorted {A} `{DecTotalOrder A} : list A -> Prop :=
| Sorted_0 : Sorted []
| Sorted_1 : forall x, Sorted [x]
| Sorted_2 : forall x y l, leb x y ->
                           Sorted (y :: l) ->
                           Sorted (x :: y :: l).

Definition GeLst `{DecTotalOrder} x l :=
  List.Forall (fun y => leb y x) l.

Definition LeLst `{DecTotalOrder} x l :=
  List.Forall (leb x) l.

Lemma lem_sorted_tail `{DecTotalOrder} :
  forall l x, Sorted (x :: l) -> Sorted l.
Proof.
  inversion 1; sauto.
Qed.

Lemma lem_partition `{DecTotalOrder} :
  forall x l1 l2, Sorted l1 -> Sorted l2 -> GeLst x l1 -> LeLst x l2 ->
                  Sorted (l1 ++ x :: l2).
Proof.
  induction l1.
  - inversion 4; sauto lq: on.
  - inversion 1; inversion 2; hauto use: lem_sorted_tail ctrs: Sorted.
Qed.

Lemma lem_all_forall {A} `{DecTotalOrder A} (P : A -> Prop) :
  forall t, All P t -> List.Forall P (elements t).
Proof.
  induction 1.
  - constructor.
  - sintuition use: List.Forall_app.
Qed.

Lemma lem_elements `{DecTotalOrder} :
  forall t, BST t -> Sorted (elements t).
Proof.
  induction 1 as [|x l r].
  - sauto.
  - simpl.
    assert (GeLst x (elements l)).
    { sfirstorder use: lem_all_forall. }
    assert (LeLst x (elements r)).
    { apply List.Forall_impl with (P := ltb x);
        auto using lem_ltb_to_leb, lem_all_forall. }
    auto using lem_partition.
Qed.

(*********************************************************************)
(* member *)

Fixpoint member `{DecTotalOrder} x t :=
  match t with
  | empty => false
  | node y l r =>
    if eq_dec x y then
      true
    else
      if leb_ltb_dec x y then
        member x l
      else
        member x r
  end.

Lemma lem_member `{DecTotalOrder} :
  forall x t, member x t -> List.In x (elements t).
Proof.
  induction t.
  - sauto.
  - hauto lq: on rew: off use: List.in_elt, List.in_or_app.
Qed.

Lemma lem_all_in_left {A} `{DecTotalOrder A} :
  forall x l1 l2, List.In x (l1 ++ l2) ->
                  List.Forall (fun y : A => x <> y) l2 -> List.In x l1.
Proof.
  induction l1.
  - induction l2; sauto.
  - sauto.
Qed.

Lemma lem_all_in_right {A} `{DecTotalOrder A} :
  forall x l1 l2, List.In x (l1 ++ l2) ->
                  List.Forall (fun y : A => x <> y) l1 -> List.In x l2.
Proof.
  induction l1.
  - induction l2; sauto.
  - sauto.
Qed.

Lemma lem_member_rev `{DecTotalOrder} :
  forall x t, BST t -> List.In x (elements t) -> member x t.
Proof.
  induction 1 as [|y l r A1 A2 B1 IH1 B2 IH2].
  - sauto.
  - simpl.
    destruct (eq_dec x y); [ sauto | idtac ].
    destruct (leb_ltb_dec x y).
    + assert (List.Forall (ltb x) (elements r)).
      { qauto use: lem_all_forall, lem_all_ltb_trans. }
      assert (List.Forall (ltb x) (y :: elements r)).
      { sauto use: lem_ltb_spec. }
      assert (List.Forall (fun z => x <> z) (y :: elements r)).
      { eapply (List.Forall_impl (P := ltb x)); auto.
        sauto use: lem_ltb_spec. }
      hauto lq: on use: lem_all_in_left.
    + assert (List.Forall (fun z => x <> z) (elements l)).
      { qauto use: lem_all_forall, lem_all_leb_ltb_eq, lem_ltb_not_leb. }
      sfirstorder use: lem_all_in_right.
Qed.

(*********************************************************************)
(* insert *)

Fixpoint insert `{DecTotalOrder} x t :=
  match t with
  | empty => node x empty empty
  | node y l r =>
    if leb_ltb_dec x y then
      node y (insert x l) r
    else
      node y l (insert x r)
  end.

Lemma lem_insert_member `{DecTotalOrder} :
  forall x t, member x (insert x t).
Proof.
  induction t; hauto lq: on rew: off.
Qed.

Lemma lem_insert_perm `{DecTotalOrder} :
  forall x t, Permutation (x :: elements t) (elements (insert x t)).
Proof.
  induction t; hauto use: Permutation, Permutation_middle.
Qed.

Lemma lem_insert_all {A} `{DecTotalOrder A} (P : A -> Prop) :
  forall x t, P x -> All P t -> All P (insert x t).
Proof.
  induction 2; sauto.
Qed.

Lemma lem_insert_bst `{DecTotalOrder} :
  forall x t, BST t -> BST (insert x t).
Proof.
  induction 1; hauto l: on use: lem_insert_all.
Qed.

(*********************************************************************)
(* maximum *)

Fixpoint maximum {A} `{DecTotalOrder A} (t : tree A) : t <> empty -> A :=
  match t with
  | empty => fun p => match p eq_refl with end
 | node x l r => fun _ =>
                    match r as r' return r = r' -> A with
                    | empty => fun _ => x
                    | node _ _ _ => fun p => maximum r ltac:(congruence)
                    end eq_refl
  end.

Lemma lem_maximum_eq `{DecTotalOrder} :
  forall x l x' l' r' p, exists p',
      maximum (node x l (node x' l' r')) p = maximum (node x' l' r') p'.
Proof.
  intros.
  unshelve eexists; [ discriminate | reflexivity ].
Qed.

Lemma lem_maximum_node `{DecTotalOrder} :
  forall t, BST t ->
            forall x l r p, t = node x l r -> leb x (maximum t p).
Proof.
  induction 1 as [|x0 l0 r0 A1 A2 B1 IH1 B2 IH2].
  - sauto.
  - intros x l r p.
    inversion 1; subst.
    destruct r as [|x' l' r'].
    + sauto use: leb_refl.
    + destruct (lem_maximum_eq x l x' l' r' p) as [p' HH].
      rewrite HH.
      enough (leb x' (maximum (node x' l' r') p')).
      { inversion A2; subst.
        eauto using leb_trans, lem_ltb_to_leb. }
      eauto.
Qed.

Lemma lem_maximum `{DecTotalOrder} :
  forall t, BST t -> forall p, All (fun y => leb y (maximum t p)) t.
Proof.
  induction 1 as [|x l r A1 A2 B1 IH1 B2 IH2].
  - sauto.
  - intro p.
    constructor.
    + eapply lem_maximum_node; sauto.
    + sauto lq: on use: lem_maximum_node, lem_all_trans, leb_trans.
    + destruct r; sfirstorder use: lem_maximum_eq.
Qed.

Lemma lem_maximum_in `{DecTotalOrder} :
  forall t p, List.In (maximum t p) (elements t).
Proof.
  induction t as [|x l IH1 r IH2].
  - sauto.
  - simpl elements.
    intro p.
    destruct r.
    + hauto lq: on use: List.in_app_iff.
    + hauto qb: on rew: off use: lem_maximum_eq, List.in_app_iff.
Qed.

Lemma lem_maximum_all {A} `{DecTotalOrder A} (P : A -> Prop) :
  forall t p, All P t -> P (maximum t p).
Proof.
  qauto use: lem_maximum_in, lem_all_forall, List.Forall_forall.
Qed.

(*********************************************************************)
(* deletemax *)

Fixpoint deletemax {A} `{DecTotalOrder A} (t : tree A) : tree A :=
  match t with
  | empty => empty
  | node x l r =>
    match r with
    | empty => l
    | node _ _ _ => node x l (deletemax r)
    end
  end.

Lemma lem_deletemax_eq `{DecTotalOrder} :
  forall x l x' l' r',
    elements (deletemax (node x l (node x' l' r'))) =
    elements l ++ x :: elements (deletemax (node x' l' r')).
Proof.
  reflexivity.
Qed.

Lemma lem_deletemax_perm `{DecTotalOrder} :
  forall t p, Permutation (maximum t p :: elements (deletemax t)) (elements t).
Proof.
  induction t as [|x l IH1 r IH2].
  - sauto.
  - intro p.
    destruct r as [|x' l' r'].
    + simpl. eauto using Permutation_cons_append.
    + destruct (lem_maximum_eq x l x' l' r' p) as [p' HH].
      rewrite HH.
      rewrite lem_deletemax_eq.
      rewrite List.app_comm_cons.
      simpl elements at 3.
      eauto using Permutation, Permutation_app, Permutation_middle.
Qed.

Lemma lem_deletemax_all {A} `{DecTotalOrder A} (P : A -> Prop) :
  forall t, All P t -> All P (deletemax t).
Proof.
  induction 1.
  - sauto.
  - destruct r; sauto lq: on.
Qed.

Lemma lem_deletemax_bst `{DecTotalOrder} :
  forall t, BST t -> BST (deletemax t).
Proof.
  induction 1.
  - sauto.
  - simpl.
    destruct r; sauto lq: on use: lem_deletemax_all.
Qed.

(*********************************************************************)
(* delete *)

Fixpoint delete {A} `{DecTotalOrder A} (x : A) (t : tree A) : tree A :=
  match t with
  | empty => empty
  | node y l r =>
    if eq_dec x y then
      match l as l' return l = l' -> tree A with
      | empty => fun _ => r
      | node _ _ _ => fun p =>
                        node (maximum l ltac:(congruence)) (deletemax l) r
      end eq_refl
    else
      if leb_ltb_dec x y then
        node y (delete x l) r
      else
        node y l (delete x r)
  end.

Lemma lem_delete_member `{DecTotalOrder} :
  forall x t, member x t ->
              Permutation (elements t) (x :: elements (delete x t)).
Proof.
  induction t as [|y l IH1 r IH2].
  - sauto.
  - simpl member.
    simpl delete.
    destruct (eq_dec x y).
    + subst.
      destruct l as [|x l1 l2].
      * simpl.
        eauto using Permutation.
      * generalize_proofs.
        intro p.
        intro.
        change (Permutation (elements (node x l1 l2) ++ y :: elements r)
                            (y :: elements (deletemax (node x l1 l2)) ++
                               maximum (node x l1 l2) p :: elements r)).
        eapply perm_trans;
          [ eapply Permutation_sym; eapply Permutation_middle | idtac ].
        (* "hauto" bug: leaves a subgoal *)
        eauto using Permutation, Permutation_sym, Permutation_middle, Permutation_app, lem_deletemax_perm.
    + destruct (leb_ltb_dec x y).
      * intro.
        change (Permutation (elements l ++ y :: elements r)
                            ((x :: elements (delete x l)) ++ y :: elements r)).
        eauto using Permutation_app.
      * intro.
        change (Permutation (elements l ++ y :: elements r)
                            (x :: elements l ++ y :: elements (delete x r))).
        apply Permutation_sym.
        eapply Permutation_trans.
        apply Permutation_middle.
        apply Permutation_app; trivial.
        eauto using Permutation, Permutation_cons, Permutation_sym.
Qed.

Lemma lem_delete_nonmember `{DecTotalOrder} :
  forall x t, ~ member x t -> delete x t = t.
Proof.
  induction t as [|y l IH1 r IH2].
  - sauto.
  - simpl.
    destruct (eq_dec x y).
    + hauto l: on.
    + hauto q: on.
Qed.

Lemma lem_delete_all {A} `{DecTotalOrder A} (P : A -> Prop) :
  forall x t, All P t -> All P (delete x t).
Proof.
  induction 1 as [| y l r ].
  - sauto.
  - simpl.
    destruct (eq_dec x y).
    + destruct l; sauto lq: on use: lem_maximum_all, lem_deletemax_all.
    + destruct (leb_ltb_dec x y); constructor; auto.
Qed.

Lemma lem_delete_bst `{DecTotalOrder} :
  forall x t, BST t -> BST (delete x t).
Proof.
  intros x t.
  sdestruct (member x t).
  - induction 1 as [|y l r A1 A2 B1 IH1 B2 IH2].
    + sauto.
    + simpl in *.
      destruct (eq_dec x y).
      * subst.
        destruct l as [|z l1 l2]; trivial.
        generalize_proofs.
        intro p.
        assert (List.Forall (fun y' => leb y' y) (elements (node z l1 l2))).
        { apply lem_all_forall.
          eapply lem_all_trans; eauto. }
        sauto lq: on use: lem_deletemax_bst, lem_all_ltb_trans, lem_deletemax_all, lem_maximum, List.Forall_forall, lem_maximum_in.
      * destruct (leb_ltb_dec x y); sauto lq: on use: lem_delete_all.
  - sauto lq: on use: lem_delete_nonmember.
Qed.
