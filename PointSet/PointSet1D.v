(** * A 1-D set of points *)
Require Export PointSet.Naive Point.NatPoint1D SplitMarker.Image1D.
Module PointSet1D := NaivePointSet NatPoint1D ImageSplitMarker1D.
