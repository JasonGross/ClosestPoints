Require Export CommonDefinitions Point.NatPointCore2D.

(** We implement the brute force algorithm as a sanity check *)
Fixpoint n2_brute_force (pts : list point) : option nat
  := match pts with
       | nil => None
       | pt::pts' => fold_left option_min
                               (map (fun pt' => Some ∥ pt' -- pt ∥²)
                                    pts')
                               (n2_brute_force pts')
     end.
