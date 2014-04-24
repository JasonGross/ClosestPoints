(** * The strip around the median *)
Require Export Point.Core.

Module Type Strip (point : Point).
  Import point.Notations.

  Axiom get_closest_points_in_strip
  : forall (median : point.t)
           (pre_closest_pair : point.t * point.t)
           (strip : list point.t),
      point.t * point.t.

  Section correct.
    Context (median : point.t)
            (pre_closest_pair : point.t * point.t)
            (strip : list point.t).

    Let post_closest_pair := get_closest_points_in_strip median pre_closest_pair strip.

    Axiom get_closest_points_in_strip_closer
    : (∥' fst post_closest_pair -- snd post_closest_pair '∥
        ≤ ∥' fst pre_closest_pair -- snd pre_closest_pair '∥)%dist.

    (*Axiom get_closest_points_in_strip_closest
    : List.(∥' fst post_closest_pair -- snd post_closest_pair '∥
        ≤ ∥' fst pre_closest_pair -- snd pre_closest_pair '∥)%dist.

    Axiom get_closest_points_in_strip_in_strip
    : (∥' fst post_closest_pair -- snd post_closest_pair '∥
        ≤ ∥' fst pre_closest_pair -- snd pre_closest_pair '∥)%dist.*)
  End correct.
End Strip.
