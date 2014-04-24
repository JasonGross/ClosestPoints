(** * Markers on splits of the data set *)
Require Export Point.Core.

Module Type SplitMarker (point : Point).
  Axiom t : Type.
  Axiom make_split_marker : forall (left : list point.t)
                                   (median : option point.t)
                                   (right : list point.t),
                              t.
End SplitMarker.
