(** * A type of Points *)
Require Export CommonDefinitions.
(** We parameterize over a type of points. *)
(** A [Point] is a [Type] together with a type of distances between points. *)
Module Type Point.
  Axiom t : Type.
  Axiom distT : Type.
  Axiom dist_le : distT -> distT -> Prop.
  Axiom get_dist : t -> t -> distT.
  Axiom x_le : t -> t -> Prop.
  Context `{x_le_dec : forall x y, Decidable (x_le x y),
              dist_le_dec : forall x y, Decidable (dist_le x y)}.

  Axiom point_in_strip_close_enough : t -> distT -> t -> bool.

  Axiom min_dist : distT -> distT -> distT.

  Context `{x_le_preo : PreOrder _ x_le, dist_le_preo : PreOrder _ dist_le}.
  Context `{x_le_paro : @PartialOrder _ eq _ x_le _, dist_le_paro : @PartialOrder _ eq _ dist_le _}.
  Context `{x_le_total : Total _ x_le, dist_le_total : Total _ dist_le}.

  Module Import Notations.
    Delimit Scope dist_scope with dist.
    Delimit Scope dec_dist_scope with dec_dist.

    Infix "<=" := x_le : type_scope.
    Infix "<=" := x_le_dec : dec_scope.
    Infix "<=" := dist_le : dist_scope.
    Infix "<=" := dist_le_dec : dec_dist_scope.

    Infix "≤" := x_le : type_scope.
    Infix "≤" := x_le_dec : dec_scope.
    Infix "≤" := dist_le : dist_scope.
    Infix "≤" := dist_le_dec : dec_dist_scope.

    Notation "∥' x -- y '∥" := (get_dist x y).
  End Notations.
End Point.
