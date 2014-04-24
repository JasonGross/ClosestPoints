Require Export Point.Core2D PointSet.Core.

Module Type PointSet2D (point : Point2D) <: PointSet point.
  Include PointSet point.
End PointSet2D.
