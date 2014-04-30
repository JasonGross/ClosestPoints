Require Export Point.Core2D Point.NatPoint1D Point.NatPointCore2D CommonDefinitions.

Module NatPoint2D <: Point2D.
  Definition t := point.
  Definition distT := nat.
  (*Definition min_dist := min.*)
  Definition get_dist (x y : point) := ∥ x -- y ∥².
  Definition x_le p1 p2 := le p1.(x) p2.(x).
  Definition y_le p1 p2 := le p1.(y) p2.(y).
  Definition x_le_dec : forall x y, {x_le x y} + {~x_le x y}
    := fun _ _ => le_dec _ _.
  Definition y_le_dec : forall x y, {y_le x y} + {~y_le x y}
    := fun _ _ => le_dec _ _.
  Definition point_in_strip_close_enough (pt1 : t) (max_square_distance : distT) (pt2 : t) : bool
    := if ((Nat.max (pt1.(y) - pt2.(y)) (pt2.(y) - pt1.(y))) ^ 2 <= 2 * max_square_distance)%dec
       then true
       else false.

  Definition dist_le : distT -> distT -> Prop := le.

  Definition dist_le_dec := le_dec.
  Instance x_le_preo : PreOrder x_le := _.
  Admitted.
  Instance dist_le_preo : PreOrder dist_le := _.
  Instance x_le_paro : @PartialOrder _ eq _ x_le x_le_preo := _.
  Admitted.
  Instance dist_le_paro : @PartialOrder _ eq _ dist_le dist_le_preo := _.
  Instance x_le_total : Total x_le := _.
  Admitted.
  Instance dist_le_total : Total dist_le := _.

  Definition min_dist (x y : distT) : distT
    := if dist_le_dec x y then x else y.

  Module Notations.
  End Notations.
End NatPoint2D.
