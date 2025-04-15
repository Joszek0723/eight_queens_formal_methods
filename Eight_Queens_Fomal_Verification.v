Require Import List Arith Lia.
Import ListNotations.

(* A board is a list of column indices; index is the row *)
Definition board := list nat.

Fixpoint abs (n m : nat) : nat :=
  if leb n m then m - n else n - m.

Fixpoint safe (col : nat) (rest : board) (row_offset : nat) : Prop :=
  match rest with
  | [] => True
  | c' :: rest' =>
      col <> c' /\ abs col c' <> row_offset /\ safe col rest' (S row_offset)
  end.

Fixpoint valid (b : board) : Prop :=
  match b with
  | [] => True
  | c :: rest => safe c rest 1 /\ valid rest
  end.

Fixpoint safeb (col : nat) (rest : board) (row_offset : nat) : bool :=
  match rest with
  | [] => true
  | c' :: rest' =>
      if Nat.eqb col c' then false
      else if Nat.eqb (abs col c') row_offset then false
      else safeb col rest' (S row_offset)
  end.

Fixpoint validb (b : board) : bool :=
  match b with
  | [] => true
  | c :: rest => safeb c rest 1 && validb rest
  end.

Definition is_valid_board (b : board) : bool := validb b.

Definition board_length n (b : board) := length b = n.

Definition validb_spec : forall b, validb b = true <-> valid b.
Proof.
  induction b as [|x xs IH]. 
  * simpl. split; auto.
  * simpl. rewrite Bool.andb_true_iff. destruct (IH) as [IH1 IH2].
    split.
    + intros [H1 H2].
      induction xs as [|y ys IHs].
      - simpl in H1. constructor. auto.
      - simpl in H1. repeat (apply andb_prop in H1 as [-> H1]); repeat (apply Bool.negb_true_iff in H1).
        repeat rewrite Nat.eqb_neq in *. rewrite Nat.eqb_eq in *.
        simpl. repeat split; auto.
    + intros [[Hneq Habs] Hval]. 
      rewrite IH2 in Hval. clear IH2.
      revert Hneq Habs. generalize 1.
      induction xs as [|y ys IHs]; intros n0 Hneq Habs.
      - simpl. reflexivity.
      - simpl. rewrite Nat.eqb_neq in Hneq. rewrite Nat.eqb_neq in Habs.
        rewrite Hneq, Habs, IHs; auto.
Qed.

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

(* Generate all permutations of a list *)
Fixpoint insert_all (x : nat) (l : list nat) : list (list nat) :=
  match l with
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: map (fun zs => y :: zs) (insert_all x ys)
  end.

Fixpoint perms (l : list nat) : list (list nat) :=
  match l with
  | [] => [[]]
  | x :: xs => concat (map (insert_all x) (perms xs))
  end.

(* Generate [1; 2; ...; n] *)
Fixpoint range (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => range n' ++ [n]
  end.

Definition all_valid_boards (n : nat) : list board :=
  filter is_valid_board (perms (range n)).

Definition n_queens_solutions (n : nat) : list board :=
  all_valid_boards n.

Fixpoint safe_partial (col : nat) (queens : board) (row_offset : nat) : bool :=
  match queens with
  | [] => true
  | c' :: qs =>
      if (Nat.eqb col c' || Nat.eqb (abs col c') row_offset)%nat
      then false
      else safe_partial col qs (S row_offset)
  end.

Fixpoint solve_nqueens (n k : nat) (partial : board) : list board :=
  match k with
  | 0 => [partial]
  | S k' =>
      flat_map (fun col =>
        if safe_partial col partial 1
        then solve_nqueens n k' (col :: partial)
        else []) (seq 1 n)
  end.

Definition n_queens_fast (n : nat) : list board :=
  solve_nqueens n n [].

Lemma validb_valid : forall b, validb b = true -> valid b.
Proof.
  intros b H. apply validb_spec. exact H.
Qed.

Lemma valid_validb : forall b, valid b -> validb b = true.
Proof.
  intros b H. apply validb_spec. exact H.
Qed.

Lemma solve_nqueens_correct : forall n b,
  In b (n_queens_fast n) -> valid b /\ length b = n.
Proof.
  intros n b.
  unfold n_queens_fast.
  generalize dependent b.
  induction n as [|n' IH]; intros b Hb.
  - simpl in Hb. destruct Hb as [Hb | []]. subst. split; simpl; auto.
  - simpl in Hb.
    unfold seq in Hb.
    remember (flat_map _ (seq 1 (S n'))) as boards.
    induction (seq 1 (S n')) as [|c cs IHcs]. simpl in Hb. contradiction.
    simpl in Hb. apply in_app_or in Hb as [Hleft | Hright].
    + destruct (safe_partial c [] 1) eqn:Hsafe.
      * simpl in Hleft. apply IH in Hleft as [Hval Hlen].
        split.
        -- simpl. apply Hval.
        -- simpl. rewrite Hlen. reflexivity.
      * simpl in Hleft. contradiction.
    + apply IHcs in Hright. exact Hright.
Qed.

Lemma in_perms_range : forall n b,
  In b (perms (range n)) -> length b = n /\ NoDup b /\ Forall (fun x => 1 <= x <= n) b.
Proof.
  intros n b.
  induction n as [|n' IH]; intros H.
  - simpl in H. destruct H as [H | []]. subst. simpl. repeat split; constructor.
  - simpl in H. apply in_concat_map_inv in H as [xs [Hxs Hinx]].
    apply IH in Hinx as [Hlen [Hnd Hbound]].
    destruct (in_insert_all_inv _ _ _ Hxs) as [Hins Hlen'].
    subst. repeat split.
    + simpl. lia.
    + inversion Hnd; subst. constructor; auto.
      intro Hin. apply H0. apply in_map with (f := fun zs => y :: zs) in Hin. exact Hin.
    + constructor; auto.
Qed.

Lemma equivalent_solutions : forall n b,
  In b (n_queens_solutions n) <-> In b (n_queens_fast n).
Proof.
  intros n b.
  split.
  - intros Hin.
    unfold n_queens_solutions, all_valid_boards, is_valid_board in Hin.
    apply filter_In in Hin as [Hperm Hvb].
    apply validb_valid in Hvb.
    (* We'll reconstruct this board by backtracking *)
    assert (length b = n /\ NoDup b /\ Forall (fun x => 1 <= x <= n) b).
    { apply in_perms_range. exact Hperm. }
    destruct H as [Hlen _].
    (* Now show that any valid board is generated by solve_nqueens *)
    (* We build an induction on length of b *)
    revert b Hvb Hlen. induction n as [|n' IH]; intros b Hval Hlen.
    + destruct b; simpl in *; try discriminate. now left.
    + destruct b as [|c rest]; simpl in *; try discriminate.
      simpl.
      remember (safe_partial c rest 1) as sc.
      assert (safe_partial c rest 1 = true).
      { rewrite <- Heqsc. apply valid_validb. exact Hval. }
      rewrite H. simpl.
      apply in_flat_map. exists c. split.
      * apply in_seq. lia.
      * apply IH; simpl in Hlen; lia.
  - intros Hin.
    apply solve_nqueens_correct in Hin as [Hvalid Hlen].
    apply valid_validb in Hvalid.
    apply filter_In. split.
    + apply in_perms_range. unfold n_queens_solutions, all_valid_boards. apply in_seq. lia.
    + exact Hvalid.
Qed.
