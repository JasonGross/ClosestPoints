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

Goal True.
  pose (@ClosestPoints1D.make_algorithm_tree_from_point_set
          _ (1::5::2::15::13::[])%vector).
  hnf in s.
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
