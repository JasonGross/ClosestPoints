(** * 1-D image split marker *)
Require Export Point.NatPoint1D SplitMarker.Core.

Module ImageSplitMarker1D <: SplitMarker NatPoint1D.
  Module point := NatPoint1D.
  (** An image has a list of points in the grid, and a list of line locations. *)
  Definition t := (list point.t * list point.t)%type.
  Definition make_split_marker
             (left : list point.t)
             (median : option point.t)
             (right : list point.t)
  : t
    := ((left ++ right)%list,
        match median with
          | Some pt => [pt]
          | _ => nil
        end).
End ImageSplitMarker1D.
