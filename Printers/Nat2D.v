(** ** Print 2-D grid of nats *)
Require Export Ascii String.
Require Export Point.NatPoint2D.

Local Open Scope string_scope.
Local Open Scope list_scope.

Module GridPrinter.
  Local Transparent point pt_x pt_y Build_point.

  Fixpoint add_to_row (x : nat) (l : list bool) : list bool :=
    match x with
      | 0 => match l with
               | nil => true::nil
               | x::xs => true::xs
             end
      | S x' => match l with
                  | nil => false
                  | l0::ls => l0
                end::add_to_row x' l
    end.

  Fixpoint add_to_grid (x y : nat) (g : list (list bool)) : list (list bool)
    := match y with
         | 0 => match g with
                  | nil => (add_to_row x nil)::nil
                  | r::rs => (add_to_row x r)::rs
                end
         | S y' => match g with
                     | nil => nil::add_to_grid x y' nil
                     | r::rs => r::add_to_grid x y' rs
                   end
       end.

  Fixpoint list_to_grid (l : list point) (g : list (list bool)) : list (list bool) :=
    match l with
      | nil => g
      | pt::ls => list_to_grid ls (add_to_grid pt.(x) pt.(y) g)
    end.

  Fixpoint row_to_string (lines : nat -> string) (l : list bool) : string :=
    ((lines 0)
       ++ match l with
            | nil => EmptyString
            | b::ls => (if b then "*"(*•*) else " ")
                         ++ (row_to_string (fun n => lines (S n)) ls)
          end)%string.

  Fixpoint repeat {T} (n : nat) (v : T) :=
    match n with
      | 0 => nil
      | S n' => v::repeat n' v
    end.

  Definition pad_right {T} (default : T) (new_len : nat) (l : list T) : list T :=
    l ++ repeat (new_len - List.length l) default.

  Definition normalize_grid {T} (g : list (list T)) (default : T) :=
    let max_length := fold_left Arith.Max.max (map (@List.length _) g) 0 in
    map (pad_right default max_length) g.

  Definition string_list_of_grid (lines : nat -> string) (grid : list (list bool)) : list string :=
    map (row_to_string lines) (normalize_grid grid false).

  Definition string_list_of_coords (lines : nat -> string) (points : list point) : list string :=
    string_list_of_grid lines (list_to_grid points nil).

  Ltac print_grid grid :=
    match eval compute in grid with
      | nil => idtac ""
      | ?r::?rs => idtac r; print_grid rs
    end.

  Ltac print_list l := print_grid (string_list_of_coords (fun _ => "") l).
  Ltac print_list_with_lines l lines :=
    print_grid (string_list_of_coords (fun x =>
                                         match lines with
                                           | nil => " "
                                           | x0::xs => if eq_nat_dec x0 x then "|"
                                                       else if in_dec eq_nat_dec x lines then ":"(*"⋮"*)
                                                            else " "
                                         end)
                                      l).
  Goal True.
    print_list ((1,1)::(2,3)::(4,5)::nil).
    print_list_with_lines ((1,1)::(2,3)::(4,5)::nil) (3::nil).
    print_list_with_lines ((1,1)::(2,3)::(4,5)::nil) (2::3::nil).
  Abort.
End GridPrinter.
