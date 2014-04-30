(** * Non-negative integer 1-D points *)
Require Export NArith.
Require Export Point.Core.

Module NatPoint1D <: Point.
  Definition t := nat.
  Definition distT := nat.
  (*Definition min_dist := min.*)
  Definition get_dist (x y : t) := ∥' x -- y '∥.
  Definition x_le : t -> t -> Prop := le.
  Definition dist_le : distT -> distT -> Prop := le.

  Definition x_le_dec := le_dec.
  Definition dist_le_dec := le_dec.
  Instance x_le_preo : PreOrder x_le := _.
  Instance dist_le_preo : PreOrder dist_le := _.
  Instance x_le_paro : @PartialOrder _ eq _ x_le x_le_preo := _.
  Instance dist_le_paro : @PartialOrder _ eq _ dist_le dist_le_preo := _.
  Instance x_le_total : Total x_le := _.
  Instance dist_le_total : Total dist_le := _.

  Definition min_dist (x y : distT) : distT
    := if dist_le_dec x y then x else y.

  Module Notations.
  End Notations.

  (** We take in the median point, the smallest distance we know
      about, and another point.  We say that a point is in the strip
      if its distance to the median is less than or equal to the
      smallest distance we know about. *)
  Definition point_in_strip_close_enough : t -> distT -> t -> bool
    := fun pt1 dist pt2 => if (∥' pt1 -- pt2 '∥ ≤ dist)%dec then true else false.
End NatPoint1D.
