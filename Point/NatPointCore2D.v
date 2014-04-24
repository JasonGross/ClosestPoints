Require Export Arith NPeano.

Definition point := prod nat nat.
Bind Scope point_scope with point.
Delimit Scope point_scope with point.
Definition pt_x : point -> nat := @fst _ _.
Definition pt_y : point -> nat := @snd _ _.
Definition Build_point : nat -> nat -> point := pair.
Opaque point pt_x pt_y Build_point.
Notation "( x , y , .. , z )" := (Build_point .. (Build_point x y) .. z) : point_scope.

Notation "p '.(x)'" := (pt_x p) (at level 5, no associativity).
Notation "p '.(y)'" := (pt_y p) (at level 5, no associativity).

Section distance.
  Definition abs_minus (x y : nat) :=
    if le_dec x y then y - x else x - y.
  Local Infix "-" := abs_minus.

  Definition square_distance (x1 y1 x2 y2 : nat) := (x1 - x2)^2 + (y1 - y2)^2.
End distance.

Definition point_square_distance (p1 p2 : point) := square_distance p1.(x) p1.(y) p2.(x) p2.(y).

Notation "∥ p1 -- p2 ∥²" := (point_square_distance p1 p2) : nat_scope.
