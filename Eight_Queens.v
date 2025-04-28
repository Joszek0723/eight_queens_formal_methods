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

(*
The safe function checks if a queen can be placed in a given column without threatening any other queens.
It takes three parameters:
- col: The column position to check
- rest: The list of existing queen positions (board state)
- row_offset: The distance from the current row being checked

The function returns a Prop (proposition) that is true if:
1. The column is not already occupied by another queen
2. The column is not on the same diagonal as any existing queen
   (diagonal check: |col - c'| ≠ row_offset)
3. The position is safe with respect to all remaining queens

This is a recursive function that checks each existing queen position against the proposed position.
*)
Fixpoint safe (col : nat) (rest : board) (row_offset : nat) : Prop :=
  match rest with
  | [] => True
  | c' :: rest' =>
      col <> c' /\ abs col c' <> row_offset /\ safe col rest' (S row_offset)
  end.

(*
The valid function checks if an entire board configuration is valid.
It takes one parameter:
- b: The board configuration to validate

Returns a Prop that is true if:
1. The board is empty (base case), or
2. The first queen is safe from all other queens, and
3. The rest of the board is also valid

This is a recursive function that validates the entire board configuration.
*)
Fixpoint valid (b : board) : Prop :=
  match b with
  | [] => True
  | c :: rest => safe c rest 1 /\ valid rest
  end.

(*
The safeb function is the boolean version of the safe function.
It takes three parameters:
- col: The column position to check
- rest: The list of existing queen positions
- row_offset: The distance from the current row

Returns a boolean that is true if the position is safe, false otherwise.
This version is used for computation rather than proof.
*)
Fixpoint safeb (col : nat) (rest : board) (row_offset : nat) : bool :=
  match rest with
  | [] => true
  | c' :: rest' =>
      if Nat.eqb col c' then false
      else if Nat.eqb (abs col c') row_offset then false
      else safeb col rest' (S row_offset)
  end.

(*
The validb function is the boolean version of the valid function.
It takes one parameter:
- b: The board configuration to validate

Returns a boolean that is true if the board is valid, false otherwise.
This version is used for computation rather than proof.
*)
Fixpoint validb (b : board) : bool :=
  match b with
  | [] => true
  | c :: rest => safeb c rest 1 && validb rest
  end.

(*
The is_valid_board function is a wrapper around validb.
It takes one parameter:
- b: The board configuration to validate

Returns a boolean indicating if the board is a valid N-Queens solution.
*)
Definition is_valid_board (b : board) : bool := validb b.

(* Example for N = 4: [2; 4; 1; 3] is a known solution *)
Definition sol4 := [2; 4; 1; 3].

Lemma sol4_valid : valid sol4.
Proof.
  unfold sol4. simpl.
  repeat split; compute; lia.
Qed.

Example test_sol4 : is_valid_board sol4 = true.
Proof. reflexivity. Qed.

Example test_invalid : is_valid_board [1; 2; 3; 4] = false.
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
  filter is_valid_board (perms (range n)).

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
The n_queens_solutions function is a wrapper around all_valid_boards.
It takes one parameter:
- n: The size of the board (N×N)

Returns all valid solutions to the N-Queens problem for an N×N board.
This function provides a clean interface to get all solutions.
*)
Definition n_queens_solutions (n : nat) : list board :=
  all_valid_boards n.

(*
The safe_partial function is an optimized version of safeb for the backtracking solution.
It takes three parameters:
- col: The column position to check
- queens: The list of existing queen positions
- row_offset: The distance from the current row

Returns a boolean that is true if the position is safe, false otherwise.
This version uses a more efficient implementation with orb for early termination.
*)
Fixpoint safe_partial (col : nat) (queens : board) (row_offset : nat) : bool :=
  match queens with
  | [] => true
  | c' :: qs =>
      if orb (Nat.eqb col c') (Nat.eqb (abs col c') row_offset)
      then false
      else safe_partial col qs (S row_offset)
  end.

(*
The solve_nqueens function implements a backtracking solution to the N-Queens problem.
It takes three parameters:
- n: The size of the board (N×N)
- k: The number of queens left to place
- partial: The current partial solution

Returns a list of all valid solutions that can be built from the partial solution.
This function:
1. Uses safe_partial to check potential queen placements
2. Recursively builds solutions by trying each valid column position
3. Uses flat_map to combine all valid solutions
*)
Fixpoint solve_nqueens (n k : nat) (partial : board) : list board :=
  match k with
  | 0 => [partial]
  | S k' =>
      flat_map (fun col =>
        if safe_partial col partial 1
        then solve_nqueens n k' (col :: partial)
        else []) (seq 1 n)
  end.

(*
The n_queens_fast function is the entry point for the efficient backtracking solution.
It takes one parameter:
- n: The size of the board (N×N)

Returns all valid solutions to the N-Queens problem for an N×N board.
This function uses the backtracking approach which is more efficient than the brute force method.
*)
Definition n_queens_fast (n : nat) : list board :=
  solve_nqueens n n [].

(* Test the efficient method *)
Eval compute in n_queens_fast 4.




(* First, let's prove the helper lemmas *)

(* Helper lemma: safe_partial is equivalent to the propositional safe *)
Lemma safe_partial_correct col rest offset :
  safe col rest offset <-> safe_partial col rest offset = true.
Proof.
  split.
  - (* Forward direction: safe -> safe_partial = true *)
    revert offset. induction rest as [|c' rest IH]; intros offset.
    + (* Base case: empty list *)
      reflexivity.
    + (* Inductive case *)
      simpl. intros [H1 [H2 H3]].
      rewrite IH by assumption.
      rewrite <- Nat.eqb_neq in H1. rewrite H1.
      rewrite <- Nat.eqb_neq in H2. rewrite H2.
      reflexivity.
  
  - (* Backward direction: safe_partial = true -> safe *)
    revert offset. induction rest as [|c' rest IH]; intros offset.
    + (* Base case: empty list *)
      reflexivity.
    + (* Inductive case *)
      simpl. destruct (col =? c') eqn:Ec; try discriminate.
      destruct (abs col c' =? offset) eqn:Ea; try discriminate.
      intros Hsafe.
      (* Convert boolean equalities to inequalities *)
      apply Nat.eqb_neq in Ec.  (* (col =? c') = false -> col <> c' *)
      apply Nat.eqb_neq in Ea.  (* (abs col c' =? offset) = false -> abs col c' <> offset *)
      split; [exact Ec|].
      split; [exact Ea|].
      apply IH.
      exact Hsafe.
Qed.

