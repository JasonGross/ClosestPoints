Require Export Div2 Even NArith NPeano.
Require Export Omega.
Require Export Point.Core PointSet.Core.
Require Export Tree.
Require Export State.Core.
Require Export CenterStrip.Core.

Module ClosestPoints (point : Point) (point_set : PointSet point) (strip : Strip point).
  (** At each node of the tree, we store the left point-set, the right point-set, and a function that takes the distance and provides us with a strip of point-lists to inspect.  At each leaf, which represents at most three points, we store the minimum square distance. *)

  Local Hint Resolve div2_decr le_n_S lt_n_S le_n_S.
  Local Hint Constructors le.
  Local Hint Extern 2 => progress hnf.
  Local Hint Extern 2 => progress simpl.
  Local Hint Extern 2 => progress subst.
  Local Hint Extern 2 => unfold lt.

  Module Export state := State point point_set.

  Lemma minus_to_plus x y z (H : x - y = S z) : x = S z + y.
  Proof.
    omega.
  Qed.

  Lemma div2_n_le_S_n n : div2 n <= S n.
  Proof.
    apply div2_decr; omega.
  Qed.

  Lemma div2_n_ne_S_S_n n : div2 n ≠ S (S n).
  Proof.
    intro H.
    pose proof (div2_n_le_S_n n) as H'.
    rewrite H in H'.
    omega.
  Qed.

  Local Ltac helper_elim_t k :=
    repeat match goal with
             | _ => assumption
             | _ => congruence
             | _ => progress subst
             | _ => progress simpl in *
             | _ => intro
             | _ => eapply div2_n_ne_S_S_n; eassumption
             | [ H : _ |- _ ] => rewrite Nat.sub_0_le in H
             | [ H : _ |- _ ] => apply le_n_0_eq in H
             | [ H : _ |- _ ] => apply div2_decr in H
             | [ H : _ |- _ ] => apply le_Sn_n in H
             | [ H : _ |- _ ] => apply le_Sn_le in H
             | [ H : _ |- _ ] => apply eq_add_S in H
             | [ H : _ |- _ ] => apply minus_to_plus in H
             | [ H : _, H' : _ |- _ ] => rewrite H in H'; clear H
             | [ |- appcontext[match ?E with _ => _ end] ] => destruct E
           end;
    match eval hnf in k with
      | S ?k' => match goal with
                   | [ n : nat |- _ ] => destruct n; progress helper_elim_t k'
                 end
      | _ => idtac
    end.

  Lemma helper_elim n3 (H : {match div2 n3 with
                               | 0 => S (S n3)
                               | 1 => S n3
                               | S (S l0) => n3 - l0
                             end = 0} +
                            {match div2 n3 with
                               | 0 => S (S n3)
                               | 1 => S n3
                               | S (S l0) => n3 - l0
                             end = 1})
  : False.
  Proof with try solve [ helper_elim_t 2 ].
    revert H; intros [ ];
    case_eq (div2 n3)...
  Qed.

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
              | n' =>
                fun H s =>
                  let split_pts := point_set.split s in
                  let median' := fst (fst split_pts) in
                  let left_set := snd (fst split_pts) in
                  let right_set := snd split_pts in
                  let left_tree' := make_algorithm_tree_from_point_set _ _ left_set in
                  let right_tree' := make_algorithm_tree_from_point_set _ _ right_set in
                  let median := match median' with
                                  | inleft median => median
                                  | inright H => match Nat.neq_succ_0 _ H : False with end
                                end in
                  let left_tree := match left_tree' with
                                     | inl t => t
                                     | inr (left eq0) => match Nat.neq_succ_0 _ eq0 with end
                                     | inr (right eq1) => match Nat.neq_succ_0 _ (Nat.succ_inj _ _ eq1) with end
                                   end in
                  let right_tree := match right_tree' with
                                      | inl t => t
                                      | inr H => match helper_elim _ H : False with end
                                    end in
                  let left_pts := match left_tree return point.t * point.t with
                                    | Leaf data => data
                                    | Node _ st _ => closest_points st
                                  end in
                  let right_pts := match right_tree return point.t * point.t with
                                     | Leaf data => data
                                     | Node _ st _ => closest_points st
                                   end in
                  let pre_closest_points := @min_by
                                              _ _ _ point.dist_le_dec
                                              (fun xy => point.get_dist (fst xy) (snd xy))
                                              left_pts right_pts in
                  let pre_min_dist := point.get_dist (fst pre_closest_points) (snd pre_closest_points) in
                  let center_strip := point_set.points_in_strip
                                 s median pre_min_dist in
                  let closest_points_in_strip := strip.get_closest_points_in_strip
                                                   median pre_closest_points center_strip in
                  let closest_points := @min_by
                                          _ _ _ point.dist_le_dec
                                          (fun xy => point.get_dist (fst xy) (snd xy))
                                          pre_closest_points
                                          closest_points_in_strip in
                  inl (Node
                         left_tree
                         {| left_points := existT _ _ left_set;
                            right_points := existT _ _ right_set;
                            median := median;
                            center_points := center_strip;
                            closest_points := closest_points;
                            closest_left_points := left_pts;
                            closest_right_points := right_pts;
                            closest_center_points := closest_points_in_strip |}
                         (*(point_set.points_sets_in_strip s)*)
                         (Some right_tree))
            end eq_refl);
    auto;
    subst;
    clear.
    cbv beta iota zeta delta [div2].
    fold div2.
    abstract (
        repeat rewrite Nat.sub_succ;
        refine (@transitivity _ _ _ _ (S _) _ _ _);
        [ unfold lt;
          apply le_n_S;
          eapply le_minus
        | auto ]
      ).
  Defined.

  Definition make_algorithm_tree_from_point_set
           (n : nat) (points : point_set.t n)
  : (tree State
          (point.t * point.t))
    + ({n = 0} + {n = 1}).
  Proof.
    revert points.
    apply (Fix lt_wf) with (x := n); clear n.
    exact make_algorithm_tree_from_point_set__helper.
  Defined.

  Section walker.
    Context {accT retT : Type}
            (handle_leaf
             : point.t * point.t
               -> accT
               -> accT * retT)
            (handle_node_before
             : State
               -> accT
               -> accT * list retT)
            (handle_node_middle
             : State
               -> accT
               -> accT * list retT)
            (handle_node_after
             : State
               -> accT
               -> accT * list retT).

    Fixpoint walk_algorithm_tree_in_order
             (tr : tree State
                        (point.t * point.t))
             (initial : accT)
             {struct tr}
    : accT * list retT
      := match tr with
           | Leaf pts => let acc_ret := handle_leaf pts initial in
                         (fst acc_ret, snd acc_ret::nil)
           | Node left_tree st right_tree =>
             let pre := handle_node_before st initial in
             let acc_ret_left := walk_algorithm_tree_in_order left_tree (fst pre) in
             let mid := handle_node_middle st (fst acc_ret_left) in
             let acc_ret_right := match right_tree with
                                    | Some tr => walk_algorithm_tree_in_order tr (fst mid)
                                    | None => (fst mid, nil)
                                  end in
             let acc_ret_after := handle_node_after st (fst acc_ret_right) in
             (fst acc_ret_after, snd pre ++ snd acc_ret_left ++ snd mid ++ snd acc_ret_right ++ snd acc_ret_after)
         end.
  End walker.
End ClosestPoints.
