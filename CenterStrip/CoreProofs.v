(** * Proofs about the strip around the median *)
Require Export CenterStrip.Core.

Module Type StripProofs (point : Point) (strip : Strip point).

  Axiom get_closest_points_in_strip_In
  : forall (median : point.t)
           (pre_closest_pair : point.t * point.t)
           (strip : list point.t)
           (ret := strip.get_closest_points_in_strip median pre_closest_pair strip),
      {ret = pre_closest_pair}
      + {List.In (fst ret) strip /\ List.In (snd ret) strip}.
End StripProofs.
