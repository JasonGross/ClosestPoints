Require Export FunctionalExtensionality.
Require Export Algorithm.Core.
Require Export PointSet.CoreProofs.
Require Export CenterStrip.CoreProofs.

Module ClosestPointsProofs (point : Point) (point_set : PointSet point) (strip : Strip point)
       (point_set_proofs : PointSetProofs point point_set)
       (strip_proofs : StripProofs point strip).
  Module Export algorithm := ClosestPoints point point_set strip.

  Local Ltac t :=
    lazy beta iota zeta;
    abstract (repeat match goal with
                       | _ => assumption
                       | _ => intro
                       | _ => progress simpl in *
                       | [ H : _ |- _ ] => apply point_set_proofs.points_in_strip_In in H
                       | [ |- appcontext[if ?E then _ else _] ] => destruct E
                       | [ |- appcontext[point_set.split ?pts] ]
                         => generalize (point_set_proofs.split_In pts);
                       destruct (point_set.split pts) as [ [? ?] ? ]
                       | _ => progress unfold min_by
                       | _ => progress split_iff
                       | _ => progress intuition
                       | [ |- appcontext[strip.get_closest_points_in_strip ?a ?b ?c] ]
                         => let H := fresh in
                            destruct (strip_proofs.get_closest_points_in_strip_In a b c) as [H|];
                       [ rewrite H
                       | ]
                     end).

  Lemma make_algorithm_tree_from_point_set__helper__contains
        (x : nat)
        (f : ∀ y : nat,
               y < x
               → point_set.t y
               → tree
                   State
                   (point.t * point.t)
                 + ({y = 0} + {y = 1}))
        (fH : forall y H pts
                     (ret := f y H pts),
                match ret with
                  | inl (Leaf pts') => point_set.In (fst pts') pts /\ point_set.In (snd pts') pts
                  | inl (Node _ pts' _) => point_set.In (fst (closest_points pts')) pts /\ point_set.In (snd (closest_points pts')) pts
                  | inr _ => True
                end)
        (pts : point_set.t x)
        (ret := @make_algorithm_tree_from_point_set__helper x f pts)
  : match ret with
      | inl (Leaf pts') => point_set.In (fst pts') pts /\ point_set.In (snd pts') pts
      | inl (Node _ pts' _) => point_set.In (fst (closest_points pts')) pts /\ point_set.In (snd (closest_points pts')) pts
      | inr _ => True
    end.
  Proof.
    destruct x; try exact I.
    destruct x; try exact I.
    destruct x; subst ret.
    { apply point_set_proofs.get_two_points_In. }
    destruct x.
    { apply point_set_proofs.get_two_closest_of_three_In. }
    lazy [make_algorithm_tree_from_point_set__helper].
    repeat (match goal with
              | [ |- appcontext[f ?y ?H ?pts] ]
                => pose proof (fH y H pts);
              generalize dependent (f y H pts)
            end;
            intros [ [?|?] | [?|?] ]).
    { Time t. }
    { Time t. }
    { Time t. }
    { Time t. }
    { Time t. }
    { Time t. }
    { Time t. }
    { Time t. }
    { Time t. }
    { Time t. }
    { Time t. }
    { Time t. }
    { Time t. }
    { Time t. }
    { Time t. }
    { Time t. }
  Qed.

  Lemma make_algorithm_tree_from_point_set__contains
        (n : nat)
        (points : point_set.t n)
        (ret := @make_algorithm_tree_from_point_set n points)
  : match ret with
      | inl (Leaf pts') => point_set.In (fst pts') points /\ point_set.In (snd pts') points
      | inl (Node _ pts' _) => point_set.In (fst (closest_points pts')) points /\ point_set.In (snd (closest_points pts')) points
      | inr _ => True
    end.
  Proof.
    revert ret.
    revert points.
    apply (Fix lt_wf) with (x := n); clear n.
    intros x fH points.
    pose proof (@make_algorithm_tree_from_point_set__helper__contains x _ fH points) as H'.
    simpl in *.
    match goal with
      | [ H : match ?E with _ => _ end |- match ?E' with _ => _ end ]
        => let H' := fresh in
           assert (H' : E' = E);
             [
             | rewrite H'; exact H ]
    end.
    clear.
    unfold make_algorithm_tree_from_point_set at 1.
    erewrite Coq.Init.Wf.Fix_eq.
    { f_equal. }
    intros.
    pose proof (functional_extensionality_dep _ _ (fun y => functional_extensionality_dep _ _ (H y))).
    subst.
    reflexivity.
  Qed.
End ClosestPointsProofs.
