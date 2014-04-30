(** * 1-D Closest Point Algorithm *)
Require Import Ascii String Sorted FMapAVL Wf Wf_nat.
Require Import Utf8.
Require Import CommonDefinitions.

Set Implicit Arguments.
Generalizable All Variables.

Local Open Scope list_scope.
Local Open Scope string_scope.

(** ** Motivation *)
(** "When doing formal program verification, take the simplest
     non-trivial relevant example.  Then take a simpler example, and
     formalize that." -- paraphrase of Adam Chlipala on best practices
     in program synthesis and verification *)

Require Import Algorithm.BruteForce.

(** ** Now we implement the axtual algorithm. *)

(** ** A type of points *)
Require Import Point.Core.

(** ** The strip around the median *)
Require Import CenterStrip.Core.

(** ** A set of points *)
Require Import PointSet.Core.

(** ** The tree with data *)
Require Import Tree.

(** ** The core algorithm *)
Require Import Algorithm.Core.

(** ** Split markers *)
Require Import SplitMarker.Core.

(** ** Naïve Point Set *)
Require Import PointSet.Naive.

(** ** The display mechanism *)
Require Import Printers.Nat.

(** ** The full algorithm *)
Require Import Algorithm.Full1D.

Lemma ne_S_0 {x} : S x <> 0. Proof. omega. Qed.
Lemma ne_SS_1 {x} : S (S x) <> 1. Proof. omega. Qed.

Goal True.
  Print ClosestPoints1D.
  pose (match @ClosestPoints1D.make_algorithm_tree_from_point_set
                _ (1::5::2::15::(*13::*)[])%vector with
          | inl x => x
          | inr (left H) => match ne_S_0 H with end
          | inr (right H) => match ne_SS_1 H with end
        end) as s.
  pose (@ClosestPoints1D.walk_algorithm_tree_in_order
          _ _
          (fun pts _ => (tt, pts))
          (fun _ _ => (tt, List.nil))
          (fun _ _ => (tt, List.nil))
          (fun st _ => (tt, (ClosestPoints1D.state.closest_points st)::List.nil))
          s
          tt) as p;
  subst s.
  lazy [(*ClosestPoints1D.walk_algorithm_tree_in_order*)
          ClosestPoints1D.make_algorithm_tree_from_point_set
          ClosestPoints1D.make_algorithm_tree_from_point_set__helper
          Fix
          Fix_F]
    in p.
  let ltwf4 := constr:(lt_wf 4) in
  let lt_wf_4 := (eval lazy in ltwf4) in
  change (lt_wf 4) with lt_wf_4 in p.
  cbv beta iota zeta in p.
  lazy [eq_ind
          eq_rect
          eq_rec] in p.
  lazy [PointSet1D.split] in p.
  match goal with
    | [ p := appcontext[vector_quick_select ?x ?y ?z ?w] |- _ ]
      => let qs := constr:(vector_quick_select x y z w) in
         let qs' := (eval lazy in qs) in
         change qs with qs' in p
  end.
  lazy [fst snd] in p.
  change ((4 - div2 4)) with 2 in p.
  lazy [Acc_inv] in p.
Eval lazy in lt_wf 4.
  cbv beta iota zeta in p.
  lazy [NatPoint.t
          NatPoint.point_in_strip_close_enough
          ImageSplitMarker.make_split_marker
          Vector.to_list
          PointSet1D.t
          NatPoint.get_dist
          NatPoint.distT
          abs_minus
          le_dec
          le_gt_dec
          le_lt_dec
          nat_rect
          nat_rec
          nat_ind
          PointSet1D.split_marker
          sumbool_rec
          sumbool_rect
          sumbool_ind
          ImageSplitMarker.t
          minus
          div2
          List.app
          NatPoint.x_le
          NatPoint.x_le_dec] in s.
  Set Printing All.

  simpl in s.
  lazy in s.
