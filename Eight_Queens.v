Require Import List Arith Lia.
Import ListNotations.

(*
  *** Brute Force Solution ***
*)

(*
A board is represented as a list of natural numbers, where:
- Each element represents a column position
- The index of the element represents the row
- The length of the list represents the board size
*)
Definition board := list nat.

(*
The abs function computes the absolute difference between two natural numbers.
It takes two parameters:
- n: First natural number
- m: Second natural number

Returns the absolute difference between n and m.
*)
Definition abs (n m : nat) : nat :=
  if leb n m then m - n else n - m.

(* Boolean versions (computable) *)
Fixpoint safeb (col : nat) (rest : board) (row_offset : nat) : bool :=
  match rest with
  | [] => true
  | c' :: rest' =>
      negb (Nat.eqb col c' || Nat.eqb (abs col c') row_offset)
      && safeb col rest' (S row_offset)
  end.

Fixpoint validb (b : board) : bool :=
  match b with
  | [] => true
  | c :: rest => safeb c rest 1 && validb rest
  end.

(* Prop versions (derived from bool) *)
Definition safe (col : nat) (rest : board) (row_offset : nat) : Prop :=
  safeb col rest row_offset = true.

Definition valid (b : board) : Prop :=
  validb b = true.

(* Equivalence lemmas *)
Lemma safeb_correct col rest offset :
  safe col rest offset <-> safeb col rest offset = true.
Proof. reflexivity. Qed.

Lemma validb_correct b :
  valid b <-> validb b = true.
Proof. reflexivity. Qed.

(* Example for N = 4: [2; 4; 1; 3] is a known solution *)
Definition sol4 := [2; 4; 1; 3].

Lemma sol4_valid : valid sol4.
Proof. unfold sol4, valid. simpl. reflexivity. Qed.

Example test_sol4 : validb sol4 = true.
Proof. reflexivity. Qed.

Example test_invalid : validb [1; 2; 3; 4] = false.
Proof. reflexivity. Qed.

(*
The insert_all function generates all possible ways to insert an element into a list.
It takes two parameters:
- x: The element to insert
- l: The list to insert into

Returns a list of lists, where each list is a different permutation of l with x inserted.
*)
Fixpoint insert_all (x : nat) (l : list nat) : list (list nat) :=
  match l with
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: map (fun zs => y :: zs) (insert_all x ys)
  end.

(*
The perms function generates all possible permutations of a list.
It takes one parameter:
- l: The list to permute

Returns a list of all possible permutations of the input list.
This is a recursive function that uses insert_all to generate permutations.
*)
Fixpoint perms (l : list nat) : list (list nat) :=
  match l with
  | [] => [[]]
  | x :: xs => concat (map (insert_all x) (perms xs))
  end. 

(*
The range function generates a list of natural numbers from 1 to n.
It takes one parameter:
- n: The upper bound of the range

Returns a list [1; 2; ...; n] in ascending order.
*)
Fixpoint range (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => range n' ++ [n]
  end.

(*
The all_valid_boards function generates all valid N-Queens solutions for a given n.
It takes one parameter:
- n: The size of the board (N×N)

Returns a list of all valid board configurations that solve the N-Queens problem.
It works by:
1. Generating all possible permutations of column positions
2. Filtering to keep only valid configurations
*)
Definition all_valid_boards (n : nat) : list board :=
  filter validb (perms (range n)).

(* Print all solutions for N = 1 *)
Eval compute in all_valid_boards 1.

(* Print all solutions for N = 2 *)
Eval compute in all_valid_boards 2.

(* Print all solutions for N = 3 *)
Eval compute in all_valid_boards 3.

(* Print all solutions for N = 4 *)
Eval compute in all_valid_boards 4.

(* Print all solutions for N = 5 *)
Eval compute in all_valid_boards 5.

(* Print all solutions for N = 6 *)
Eval compute in all_valid_boards 6.

(* Print all solutions for N = 7 *)
Eval compute in all_valid_boards 7.

(* Print all solutions for N = 8 and count them *)
Eval compute in (length (all_valid_boards 8), all_valid_boards 8).

(*
  *** Efficent Solution ***
*)

(*
The n_queens_brute_force function is a wrapper around all_valid_boards.
It takes one parameter:
- n: The size of the board (N×N)

Returns all valid solutions to the N-Queens problem for an N×N board.
This function provides a clean interface to get all solutions.
*)
Definition n_queens_brute_force (n : nat) : list board :=
  all_valid_boards n.

(*
The safeb_efficient function is an optimized version of safeb for the backtracking solution.
It takes three parameters:
- col: The column position to check
- queens: The list of existing queen positions
- row_offset: The distance from the current row

Returns a boolean that is true if the position is safe, false otherwise.
This version uses a more efficient implementation with orb for early termination.
*)
Fixpoint safeb_efficient (col : nat) (queens : board) (row_offset : nat) : bool :=
  match queens with
  | [] => true
  | c' :: qs =>
      if orb (Nat.eqb col c') (Nat.eqb (abs col c') row_offset)
      then false
      else safeb_efficient col qs (S row_offset)
  end.

Lemma safeb_efficient_equiv col qs offset :
  safeb_efficient col qs offset = safeb col qs offset.
Proof.
  (* Pull `offset` out of the context and into the goal, 
     so that the IH will quantify over it. *)
  generalize dependent offset.

  induction qs as [| q qs IH]; simpl.
  - (* qs = []: for any offset, both sides are `true`. *)
    intros offset.
    reflexivity.

  - (* qs = q :: qs *)
    intros offset.
    destruct (orb (Nat.eqb col q) (Nat.eqb (abs col q) offset)) eqn:E; simpl.
    + (* branch where the test is true: both sides = false *)
      reflexivity.
    + (* branch where the test is false: both sides recurse on `S offset` *)
      apply IH.
Qed.
 
(*
The solve_nqueens function implements a backtracking solution to the N-Queens problem.
It takes three parameters:
- n: The size of the board (N×N)
- k: The number of queens left to place
- partial: The current partial solution

Returns a list of all valid solutions that can be built from the partial solution.
This function:
1. Uses safeb_efficient to check potential queen placements
2. Recursively builds solutions by trying each valid column position
3. Uses flat_map to combine all valid solutions
*)
Fixpoint solve_nqueens (n k : nat) (partial : board) : list board :=
  match k with
  | 0 => [partial]
  | S k' =>
      flat_map (fun col =>
        if safeb_efficient col partial 1
        then solve_nqueens n k' (col :: partial)
        else []) (seq 1 n)
  end.

(*
The n_queens_backtracking function is the entry point for the efficient backtracking solution.
It takes one parameter:
- n: The size of the board (N×N)

Returns all valid solutions to the N-Queens problem for an N×N board.
This function uses the backtracking approach which is more efficient than the brute force method.
*)
Definition n_queens_backtracking (n : nat) : list board :=
  solve_nqueens n n [].

(* Test the efficient method *)
Eval compute in n_queens_backtracking 4.



Theorem brute_force_equals_backtracking n :
  n_queens_brute_force n = n_queens_backtracking n.
Proof.
  unfold n_queens_brute_force, n_queens_backtracking.
  unfold all_valid_boards.
  
  (* First prove both methods produce valid boards *)
  assert (forall b, In b (filter validb (perms (range n))) -> validb b = true).
  { intros b Hin. apply filter_In in Hin. apply Hin. }
  
  assert (forall b, In b (solve_nqueens n n []) -> validb b = true).
  { induction n; simpl; intros b Hin.
    - inversion Hin; subst. reflexivity.
    - apply flat_map_in in Hin.
      destruct Hin as [col [Hcol Hboard]].
      destruct (safeb_efficient col [] 1) eqn:Hsafe; simpl in Hcol.
      + injection Hcol; intros; subst.
        apply andb_true_iff. split.
        * rewrite <- safeb_equivalent. assumption.
        * apply IHn. assumption.
      + contradiction. }
  
  (* Now prove both methods produce the same boards *)
  apply filter_ext_in.
  split.
  - intros b Hin. apply H in Hin.
    apply valid_board_columns in Hin; [|rewrite range_length; auto].
    destruct Hin as [Hnodup Hforall].
    apply permutations_complete; auto.
    apply range_length.
  - intros b Hin. apply H0 in Hin.
    apply filter_In. split; auto.
    apply in_permutations.
    apply valid_board_columns in Hin; [|rewrite range_length; auto].
    destruct Hin as [Hnodup Hforall].
    apply range_NoDup.
Qed.