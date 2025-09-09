-- <vc-helpers>
-- </vc-helpers>

def solve (N : Nat) (A : List Nat) : List Nat :=
  sorry

theorem solve_length_prop {N : Nat} {A : List Nat} 
  (h1 : N ≥ 2) (h2 : A.length = N) :
  (solve N A).length = N - 1 := by
  sorry

theorem solve_nonincreasing_prop {N : Nat} {A : List Nat}
  (h1 : N ≥ 2) (h2 : A.length = N) :
  ∀ i, i < (solve N A).length - 1 → 
    ((solve N A).get ⟨i, sorry⟩) ≥ ((solve N A).get ⟨i+1, sorry⟩) := by
  sorry

theorem solve_nonnegative_prop {N : Nat} {A : List Nat}
  (h1 : N ≥ 2) (h2 : A.length = N) :
  ∀ x ∈ solve N A, x ≥ 0 := by
  sorry

theorem solve_consecutive_multiples {N : Nat}
  (h : N ≥ 2) :
  let A := List.range N |>.map (λ x => x + 2)
  (solve N A).length = N - 1 := by
  sorry

theorem solve_powers_of_two {N : Nat}
  (h : N ≥ 2) :
  let A := List.range N |>.map (λ x => 2^x)
  (solve N A).length = N - 1 := by
  sorry

/-
info: [3, 1, 1, 0]
-/
-- #guard_msgs in
-- #eval solve 5 [3, 6, 4, 5, 9]

-- Apps difficulty: interview
-- Assurance level: guarded