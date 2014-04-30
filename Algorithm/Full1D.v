Require Export Point.NatPoint1D PointSet.PointSet1D Algorithm.Core CenterStrip.Strip1D.

Module MidStripNat1D := MidStrip1D NatPoint1D.

Module ClosestPoints1D := ClosestPoints NatPoint1D PointSet1D MidStripNat1D.
