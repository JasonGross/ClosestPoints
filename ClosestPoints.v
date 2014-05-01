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
Import NatPrinter.

(** ** The full algorithm *)
Require Import Algorithm.Full1D.

Lemma ne_S_0 {x} : S x <> 0. Proof. omega. Qed.
Lemma ne_SS_1 {x} : S (S x) <> 1. Proof. omega. Qed.

Definition focus {T} (_ : T) := True.
Definition focusI {T} {x : T} : focus x := I.
Opaque focus.

Record LeafInfo :=
  { current_points : list NatPoint1D.t;
    closest_points : NatPoint1D.t * NatPoint1D.t }.
(*
Record ImageInfo :=
  { all_points : list ClosestPoints1D.point.t;
    current_points : list ClosestPoints1D.point.t;
 *)

Goal True.
  Print ClosestPoints1D.
  pose (1::5::2::15::13::20::12::10::11::[])%list as points.
  pose (match @ClosestPoints1D.make_algorithm_tree_from_point_set
                _ (Vector.of_list points) with
          | inl x => x
          | inr (left H) => match ne_S_0 H with end
          | inr (right H) => match ne_SS_1 H with end
        end) as s.
  lazy in s.
  Eval lazy in string_list_of_nats_with_lines points List.nil.
  Locate median.
  Print ClosestPoints1D.state.State.
  assert (p : focus
                ("                            "::(snd
                   (@ClosestPoints1D.walk_algorithm_tree_in_order
                      _ _

                      (** at the leaves, what do we do? *)
                      (** we display the other points as [.], the current points as [*], and the closest points as [o] *)
                      (fun pts lines_and_points =>
                         let disp_points' := ("o", (fst pts)::(snd pts)::[])::(".", points)::(snd lines_and_points) in
                         ((fst lines_and_points, disp_points'),
                          string_list_of_nats_with_lines_and_points
                            points
                            (fst lines_and_points)
                            disp_points'))



                      (** before each split, what do we display? *)
                      (** We display the new median line as [|], the old one as [:] *)
                      (fun st lines_and_points => let lines' := (ClosestPoints1D.state.median st)::(fst lines_and_points) in
                                       ((lines', snd lines_and_points),
                                        (string_list_of_nats_with_lines_and_points
                                           points
                                           lines'
                                           (snd lines_and_points))::List.nil))

                      (** after we come back from the left side, what do we display? *)
                      (** We display the points we care about, keeping the [o] points, but removing the [.] points *)
                      (fun st lines_and_points =>
                         let star := ("*",
                                      ((Vector.to_list (projT2 (ClosestPoints1D.state.left_points st)))
                                         ++ (Vector.to_list (projT2 (ClosestPoints1D.state.right_points st))))%list) in
                         let disp_points := match snd lines_and_points with
                                              | ("o", os)::(".", dts)::disp
                                                => ("o", os)::star::(".", points)::disp
                                              | ("o", os)::("*", _)::(".", _)::disp
                                                => ("o", os)::star::(".", points)::disp
                                              | disp => star::(".", points)::disp
                                            end in
                         let stripped_disp_points := match snd lines_and_points with
                                                       | ("o", os)::(".", dts)::disp
                                                         => disp
                                                       | ("o", os)::("*", _)::(".", _)::disp
                                                         => disp
                                                       | disp => disp
                                                     end in
                         ((fst lines_and_points, stripped_disp_points),
                          string_list_of_nats_with_lines_and_points
                            points
                            (fst lines_and_points)
                            disp_points::List.nil))


                      (** after we come back from the right side, what do we display? *)
                      (** First we display the points we care about, keeping the [o] points.
                          Then we display the center strip.
                          Then we display the center strip with the closest points on it.
                          Then we display the closest points we know about so far. *)
                      (fun st lines_and_points => (lines_and_points, (""(*ClosestPoints1D.state.closest_points st*))::List.nil))
                      s
                      (List.nil, List.nil))))) by exact focusI;
  lazy in p.
lazy [not_decidable] in p.

  lazy [not_decidable_obligation_1] in p.
  lazy [not_decidable_obligation_1] in p.
  lazy [H_subproof3] in p.
  lazy [NatPoint1D.x_le_dec] in p.
  lazy [ex_in_list_decidable_obligation_1] in p.
  lazy [list_rect list_rec list_ind] in p.
  lazy [NatPoint1D.dist_le_dec] in p.


  lazy
  simpl in p.
  lazy [abs_minus] in p.

  lazy [le_dec
          le_gt_dec
          le_lt_dec] in p.
  Set Printing All.
  lazy [
  lazy in p.
  unfold ClosestPoints1D.make_algorithm_tree_from_point_set__helper in p at 1.
  unfold ClosestPoints1D.make_algorithm_tree_from_point_set__helper in p at 1.
  unfold ClosestPoints1D.make_algorithm_tree_from_point_set__helper in p at 1.
  repeat change (fst (?x, ?y)) with x in p.
  repeat change (snd (?x, ?y)) with y in p.
  repeat change (@app _ List.nil ?x) with x in p.
  lazy [ClosestPoints1D.state.closest_points] in p.
  cbv zeta in p.
  lazy_constr_0 (div2 4) in p.
  cbv iota beta in p.
  unfold ClosestPoints1D.make_algorithm_tree_from_point_set__helper at 1 in p.
  repeat change (fst (?x, ?y)) with x in p.
  repeat change (snd (?x, ?y)) with y in p.
  repeat change (@app _ List.nil ?x) with x in p.
  lazy [ClosestPoints1D.state.closest_points] in p.
  cbv zeta in p.
  lazy_constr_0 (4 - 2) in p.
  cbv iota beta in p.
  lazy [PointSet1D.get_two_points] in p.
  repeat change (fst (?x, ?y)) with x in p.
  repeat change (snd (?x, ?y)) with y in p.
  repeat change (@app _ List.nil ?x) with x in p.
  repeat match type of p with
           | appcontext[@app _ (?x::?y) ?z]
             => change (@app _ (x::y) z) with (x::@app _ y z) in p
           | _ => progress change (@app _ List.nil ?x) with x in p
         end.
  unfold ClosestPoints1D.make_algorithm_tree_from_point_set__helper at 1 in p.
  repeat ((change (fst (?x, ?y)) with x in p)
            || (change (snd (?x, ?y)) with y in p)
            || (match type of p with
                  | appcontext[@app _ (?x::?y) ?z]
                    => change (@app _ (x::y) z) with (x::@app _ y z) in p
                  | _ => progress change (@app _ List.nil ?x) with x in p
                end)).
  unfold ClosestPoints1D.make_algorithm_tree_from_point_set__helper at 1 in p.
  repeat ((change (fst (?x, ?y)) with x in p)
            || (change (snd (?x, ?y)) with y in p)
            || (match type of p with
                  | appcontext[@app _ (?x::?y) ?z]
                    => change (@app _ (x::y) z) with (x::@app _ y z) in p
                  | _ => progress change (@app _ List.nil ?x) with x in p
                end)
            || (lazy [PointSet1D.get_two_points] in p)).
  unfold ClosestPoints1D.make_algorithm_tree_from_point_set__helper at 1 in p.
  unfold ClosestPoints1D.make_algorithm_tree_from_point_set__helper at 1 in p.
  repeat ((change (fst (?x, ?y)) with x in p)
            || (change (snd (?x, ?y)) with y in p)
            || (match type of p with
                  | appcontext[@app _ (?x::?y) ?z]
                    => change (@app _ (x::y) z) with (x::@app _ y z) in p
                  | _ => progress change (@app _ List.nil ?x) with x in p
                end)
            || (lazy [PointSet1D.get_two_points
                        PointSet1D.points_in_strip] in p)).
  unfold ClosestPoints1D.make_algorithm_tree_from_point_set__helper at 1 in p.
  unfold ClosestPoints1D.make_algorithm_tree_from_point_set__helper at 1 in p.
  unfold ClosestPoints1D.make_algorithm_tree_from_point_set__helper at 1 in p.
  unfold ClosestPoints1D.make_algorithm_tree_from_point_set__helper at 1 in p.
  repeat ((change (fst (?x, ?y)) with x in p)
            || (change (snd (?x, ?y)) with y in p)
            || (match type of p with
                  | appcontext[@app _ (?x::?y) ?z]
                    => change (@app _ (x::y) z) with (x::@app _ y z) in p
                  | _ => progress change (@app _ List.nil ?x) with x in p
                end)
            || (lazy [PointSet1D.get_two_points
                        PointSet1D.points_in_strip
                        to_list
                        filter] in p)).
  lazy [NatPoint1D.get_dist] in p.
  unfold min_by at 1 in p.
  unfold min_by at 1 in p.
  repeat ((change (fst (?x, ?y)) with x in p)
            || (change (snd (?x, ?y)) with y in p)
            || (match type of p with
                  | appcontext[@app _ (?x::?y) ?z]
                    => change (@app _ (x::y) z) with (x::@app _ y z) in p
                  | _ => progress change (@app _ List.nil ?x) with x in p
                end)
            || (lazy [PointSet1D.get_two_points
                        PointSet1D.points_in_strip
                        to_list
                        filter] in p)).
  lazy_constr_0 (abs_minus 15 15) in p.
  lazy_constr_0 (abs_minus 1 2) in p.
  lazy_constr_0 (abs_minus 5 15) in p.
  lazy_constr_0 (NatPoint1D.dist_le_dec 1 10) in p.
  cbv beta iota zeta in p.
  match type of p with
    | appcontext[@min_by ?a ?b ?c ?d ?e (?f1, ?f2) (?g1, ?g2)]
      => let term := constr:(@min_by a b c d e (f1, f2) (g1, g2)) in
         let term' := (eval lazy in term) in
         progress change term with term' in p
  end.
  do 3 match type of p with
    | appcontext[@min_by ?a ?b ?c ?d ?e (?f1, ?f2) (?g1, ?g2)]
      => let term := constr:(@min_by a b c d e (f1, f2) (g1, g2)) in
         let term' := (eval lazy in term) in
         progress change term with term' in p
  end.
  do 15 match type of p with
    | appcontext[@min_by ?a ?b ?c ?d ?e (?f1, ?f2) (?g1, ?g2)]
      => let term := constr:(@min_by a b c d e (f1, f2) (g1, g2)) in
         let term' := (eval lazy in term) in
         progress change term with term' in p
  end.
                              i
  lazy_constr_0 (@min_by (NatPoint1D.t * NatPoint1D.t)
                         NatPoint1D.distT NatPoint1D.dist_le
                         NatPoint1D.dist_le_dec
                         (λ xy : NatPoint1D.t * NatPoint1D.t,
                                 ∥' fst xy -- snd xy '∥)
                         (1, 2) (5, 15)) in p.
  Fixpoint abs_minus' (x y : nat) : nat :=
    match x, y with
      | 0, y' => y'
      | x', 0 => x'
      | S x', S y' => abs_minus' x' y'
    end.
  Arguments min_by : clear implicits.
  Eval lazy in (min_by
                  (λ xy : NatPoint1D.t * NatPoint1D.t, abs_minus' (fst xy) (snd xy))
                  (1, 2) (5, 15)).
Arguments abs_minus !x !y.


  simpl abs_minus in p.
  lazy [abs_minus] in p.
  Unset Printing Notations.

  repeat change (@app _ (?x::?y) ?z) with (x::(@app _ y z)) in p.

  repeat change (@app _ List.nil ?x) with x in p.
  match type of p with
    | appcontext[fst ?x] => let term := constr:(fst x) in
                            let term' := (eval lazy in term) in
                            change term with term' in p
  end.

  cbvbeta iota zeta in p.
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
