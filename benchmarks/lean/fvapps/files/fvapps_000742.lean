-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_uncompleted_tasks (N K M : Nat) (A B : List Nat) (C D : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_uncompleted_tasks_returns_nonneg (N K M : Nat) (A B : List Nat) (C D : List Nat)
  (h1 : N > 0) (h2 : N ≤ 100) (h3 : K ≤ 100) (h4 : M ≤ 100)
  (h5 : A.length = N) (h6 : B.length = N)
  (h7 : ∀ x ∈ A, x = 1) (h8 : ∀ x ∈ B, x = 0)
  (h9 : ∀ x ∈ C, x = 1) (h10 : ∀ x ∈ D, x = 1)
  (h11 : C.length = K) (h12 : D.length = M) :
  min_uncompleted_tasks N K M A B C D ≥ 0 :=
  sorry

theorem min_uncompleted_tasks_list_lengths_equal (N : Nat) (A B C D : List Nat)
  (h1 : N > 0) (h2 : N ≤ 100)
  (h3 : ∀ x ∈ A, x = 1) (h4 : ∀ x ∈ B, x = 0)
  (h5 : C.length ≤ 100) (h6 : D.length ≤ 100)
  (h7 : ∀ x ∈ C, x ≥ 1) (h8 : ∀ x ∈ C, x ≤ 1000)
  (h9 : ∀ x ∈ D, x ≥ 1) (h10 : ∀ x ∈ D, x ≤ 1000) :
  A.length = B.length :=
  sorry

theorem min_uncompleted_tasks_no_buttons (N : Nat) (A B : List Nat)
  (h1 : N > 0) (h2 : N ≤ 100)
  (h3 : A.length = N) (h4 : B.length = N)
  (h5 : ∀ x ∈ A, x = 1) (h6 : ∀ x ∈ B, x = 0) :
  min_uncompleted_tasks N 0 0 A B [] [] = 
  (List.zip A B).foldl (fun acc p => acc + max 0 (p.1 - p.2)) 0 :=
  sorry
-- </vc-theorems>