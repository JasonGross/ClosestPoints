Require Export Div2 Even NArith NPeano.
Require Export Point.Core PointSet.Core.
Require Export Tree.
Require Export State.Core.

Module ClosestPoints (point : Point) (point_set : PointSet point).
  (** At each node of the tree, we store the left point-set, the right point-set, and a function that takes the distance and provides us with a strip of point-lists to inspect.  At each leaf, which represents at most three points, we store the minimum square distance. *)

  Local Hint Resolve div2_decr le_n_S lt_n_S le_n_S.
  Local Hint Constructors le.
  Local Hint Extern 2 => progress hnf.
  Local Hint Extern 2 => progress simpl.
  Local Hint Extern 2 => progress subst.
  Local Hint Extern 2 => unfold lt.

  Module Export state := State point point_set.

  Definition make_algorithm_tree_from_point_set__helper
  : ∀ x : nat,
      (∀ y : nat,
         y < x
         → point_set.t y
         → tree
             State
             (point.t * point.t)
           + ({y = 0} + {y = 1}))
      → point_set.t x
      → tree
          State
          (point.t * point.t)
        + ({x = 0} + {x = 1}).
  Proof.
    intros n make_algorithm_tree_from_point_set.
    refine (match n as n' return n' = n -> point_set.t n' -> _ + ({n' = 0} + {n' = 1}) with
              | 0 => fun _ _ => inr (left eq_refl)
              | 1 => fun _ _ => inr (right eq_refl)
              | 2 => fun _ s => inl (Leaf _ (point_set.get_two_points s))
              | 3 => fun _ s => inl (Leaf _ (point_set.get_two_closest_of_three s))
              | n' => fun H s => let split_pts := point_set.split s in
                                 (*let marker := fst (fst split_pts) in*)
                                 let left_set := (*snd*) (fst split_pts) in
                                 let right_set := snd split_pts in
                                 let left_tree := make_algorithm_tree_from_point_set _ _ left_set in
                                 let right_tree := make_algorithm_tree_from_point_set _ _ right_set in
                                 inl (Node
                                        (match left_tree with
                                           | inl t => t
                                           | inr (left eq0) => match Nat.neq_succ_0 _ eq0 with end
                                           | inr (right eq1) => match Nat.neq_succ_0 _ (Nat.succ_inj _ _ eq1) with end
                                         end)
                                        {| left_points := existT _ _ left_set;
                                           right_points := existT _ _ right_set |}
                                        (*(point_set.points_sets_in_strip s))*)
                                        (match right_tree with
                                           | inl t => Some t
                                           | inr _ => None
                                         end))
            end eq_refl);
    auto;
    subst.
    cbv beta iota zeta delta [div2].
    fold div2.
    repeat rewrite Nat.sub_succ.
    refine (@transitivity _ _ _ _ (S _) _ _ _).
    * unfold lt.
      apply le_n_S.
      eapply le_minus.
    * auto.
    *
  Defined.

  Definition make_algorithm_tree_from_point_set
           (n : nat) (points : point_set.t n)
  : (tree ({ x : _ & point_set.t x } *
           { x : _ & point_set.t x } *
           point_set.split_marker *
           (point.distT -> list (point.t * { x : _ & point_set.t x })))
          point.distT)
    + ({n = 0} + {n = 1}).
  Proof.
    revert points.
    apply (Fix lt_wf) with (x := n); clear n.
    exact make_algorithm_tree_from_point_set__helper.
  Defined.

  Definition walk_algorithm_tree_in_order
             (tr : tree ({ x : _ & point_set.t x } *
                         { x : _ & point_set.t x } *
                         point_set.split_marker *
                         (point.distT -> list (point.t * { x : _ & point_set.t x })))
                        point.distT)
             (handle_node : list (point.t * { x : _ & point_set.t x }) -> point.distT)
  : list ({ x : _ & point_set.t x } *
                         { x : _ & point_set.t x } *
                         point_set.split_marker *
                         (point.distT -> list (point.t * { x : _ & point_set.t x })))
                        point.distTpoint.distT * point_set.split_marker * list (point.t * { x : _ & point_set.t x }) ).
    Print tree.
End ClosestPoints.
