Require Import List Arith Lia.
From Coq Require Import List Permutation.
Require Import Coq.Sorting.Permutation.
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
Eval compute in (length (all_valid_boards 5), all_valid_boards 5).

(* Print all solutions for N = 6 *)
Eval compute in (length (all_valid_boards 6), all_valid_boards 6).

(* Print all solutions for N = 7 *)
Eval compute in (length (all_valid_boards 7), all_valid_boards 7).

(* Print all solutions for N = 8 and count them *)
Eval compute in (length (all_valid_boards 8), all_valid_boards 8).

(*
The n_queens_brute_force function is a wrapper around all_valid_boards.
It takes one parameter:
- n: The size of the board (N×N)

Returns all valid solutions to the N-Queens problem for an N×N board.
This function provides a clean interface to get all solutions.
*)
Definition n_queens_brute_force (n : nat) : list board :=
  all_valid_boards n.

(** * Correctness of the brute-force solver

  We now turn to proving the **factual correctness** of our brute-force n-queens algorithm.
  Concretely, we must establish two key properties:

  - **Soundness**: every board the algorithm returns is indeed a valid n-queens solution.
  - **Completeness**: every valid n-queens solution of size n is found by the brute-force procedure.

  We prove these in the lemmas that follow.
*)

(*-- Soundness: every board returned really is valid *)
Lemma brute_force_sound n b :
  In b (n_queens_brute_force n) ->
  validb b = true.
Proof.
  unfold n_queens_brute_force, all_valid_boards.
  intros Hin; apply filter_In in Hin as [_ Hvalid]; exact Hvalid.
Qed.

(** [in_insert_all] characterizes the shape of any list produced by [insert_all x l]:
    every such list decomposes as [l1 ++ x :: l2], and removing [x] leaves a
    permutation of the original list [l]. *)
Lemma in_insert_all : forall x l l',
  In l' (insert_all x l) ->
  exists l1 l2, l' = l1 ++ x :: l2 /\ Permutation (l1 ++ l2) l.
Proof.
  intros x l l' Hin.
  induction l as [|y ys IH] in l', Hin |- *.
  - (* Base case: empty list *)
    simpl in Hin. destruct Hin as [H|H]; [|contradiction].
    subst l'. exists [], []. split; auto.
  - (* Inductive case: y :: ys *)
    simpl in Hin. destruct Hin as [H|H].
    + (* First case: direct insertion *)
      subst l'. exists [], (y::ys). split; auto.
    + (* Second case: recursive insertion *)
      apply in_map_iff in H. destruct H as [zs [Heq Hzs]].
      apply IH in Hzs. destruct Hzs as [l1 [l2 [Heq' Hperm]]].
      subst zs.
      exists (y::l1), l2. split.
      * (* Equality part *)
        rewrite <- Heq. simpl. reflexivity.
      * (* Permutation part *)
        apply Permutation_cons. reflexivity. assumption.
Qed.

(** Soundness of [perms]: every list returned by [perms l] is a permutation of [l]. *)
Lemma perms_sound : forall l l', In l' (perms l) -> Permutation l l'.
Proof.
  induction l as [|a l IHl]; intros l' Hin.
  - (* Base case: empty list *)
    simpl in Hin. destruct Hin as [H | H]; [subst l'; apply Permutation_refl | contradiction].
  - (* Inductive case: a::l *)
    simpl in Hin. 
    apply in_concat in Hin. destruct Hin as [l'' [Hin1 Hin2]].
    apply in_map_iff in Hin1. destruct Hin1 as [l''' [Heq Hin1]].
    subst l''.
    apply IHl in Hin1.  (* Now have Permutation l l''' *)
    clear IHl.
    (* Need to show Permutation (a::l) l' where l' is in insert_all a l''' *)
    generalize dependent l'.
    induction l''' as [|x xs IH] in a, Hin1 |- *.
    + (* Case where l''' is empty *)
      simpl. intros l' Hin2.
      destruct Hin2 as [H|H]; [subst l' | contradiction].
      simpl. apply Permutation_cons. reflexivity. apply Hin1.
    + (* Case where l''' is x::xs *)
      simpl. intros l' Hin2.
      destruct Hin2 as [H|H].
      * subst l'. apply Permutation_cons. reflexivity. assumption.
      * (* Handle the mapped case *)
        apply in_map_iff in H. destruct H as [zs [Heq' Hzs]].
        apply in_insert_all in Hzs. destruct Hzs as [l1 [l2 [Heq'' Hperm]]].
        subst zs l'.
        apply Permutation_trans with (a :: x :: l1 ++ l2). 
        apply Permutation_cons. reflexivity. 
        apply Permutation_trans with (x :: xs).
          ** apply Hin1.
          ** apply perm_skip. apply Permutation_sym, Hperm.
          ** (* First, prove that x::l1++a::l2 is a permutation of a::x::l1++l2 *)
          apply Permutation_trans with (x :: a :: l1 ++ l2).
            *** apply perm_swap.  (* Swaps a and x *)
            *** apply perm_skip.  (* Keeps x at head *)
                apply Permutation_cons_app.  (* Moves a into the list *)
                apply Permutation_refl.
Qed.

(** The simplest insertion: inserting [a] into [l2] always yields [a::l2] as one of the results. *)
Lemma insert_all_head : forall a l2, In (a :: l2) (insert_all a l2).
Proof.
  intros.
  induction l2 as [|y ys IH].
  - simpl. left. reflexivity.
  - simpl. left. reflexivity.
Qed.

(** Completeness of [perms]: every permutation of [l] appears in [perms l]. *)
Lemma perms_complete : forall l l', Permutation l l' -> In l' (perms l).
Proof.
  induction l; intros l' Hperm.
  - (* Base case for l = [] *)
    simpl.
    apply Permutation_nil in Hperm.
    subst l'.
    left; reflexivity.
  - (* Inductive case for l = a::l *)
    simpl.
    assert (In a l') as Ha.
    { apply Permutation_in with (x := a) in Hperm; [| left; reflexivity].
      assumption. }
    destruct (in_split a l') as [l1 [l2 Hl']]; [assumption|].
    subst l'.
    apply Permutation_cons_app_inv in Hperm.
    apply in_concat.
    exists (insert_all a (l1 ++ l2)).
    split.
    + apply in_map. apply IHl. apply Hperm.
    + clear IHl Hperm.
      induction l1 as [|x l1 IH].
      * apply insert_all_head.
      * (* Case l1 = x::l1 *)
        simpl.
        right.
        apply in_map.
        apply IH.
        simpl in Ha.
        destruct Ha as [Hax | Ha'].
        -- subst x. apply in_or_app. right. simpl. left. reflexivity.
        -- assumption.
Qed.

(** Completeness of brute force search: any valid board of size [n] and correct permutation
    of [range n] is found by [n_queens_brute_force n]. *)
Theorem brute_force_complete n b :
  length b = n ->
  valid b ->
  Permutation b (range n) ->
  In b (n_queens_brute_force n).
Proof.
  unfold n_queens_brute_force, all_valid_boards.
  intros Hlen Hvalid Hperm.
  apply filter_In.
  split.
  - apply perms_complete.
    apply Permutation_sym, Hperm.  (* Flip the permutation relation *)
  - apply Hvalid.
Qed.

(** The length of [range n] is exactly [n]. *)
Lemma range_length : forall n, length (range n) = n.
Proof.
  induction n as [|n IH].
  - simpl; reflexivity.
  - simpl range. rewrite app_length, IH. simpl. rewrite Nat.add_comm. reflexivity.
Qed.

(** Full correctness of the brute-force solver:
    it returns exactly those boards of length [n], valid, and permutations of [range n]. *)
Theorem brute_force_correct n b :
  In b (n_queens_brute_force n) <->
  (length b = n /\ valid b /\ Permutation b (range n)).
Proof.
  split.
  - (* Soundness direction *)
    intros Hin.
    split; [| split].
    + unfold n_queens_brute_force, all_valid_boards in Hin.
      apply filter_In in Hin as [Hperm Hvalid].
      apply perms_sound in Hperm.
      apply Permutation_length in Hperm.
      rewrite range_length in Hperm.  (* This is the key change *)
      symmetry; assumption.
    + unfold valid. (* Convert valid to validb = true *)
      apply brute_force_sound with (n := n). (* Explicitly provide n *)
      assumption.
    + unfold n_queens_brute_force, all_valid_boards in Hin.
      apply filter_In in Hin as [Hperm _].
      apply perms_sound in Hperm.
      apply Permutation_sym; assumption.
  - (* Completeness direction *)
    intros [Hlen [Hvalid Hperm]].
    apply brute_force_complete; assumption.
Qed.

(*
  *** Efficent Solution ***
*)

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