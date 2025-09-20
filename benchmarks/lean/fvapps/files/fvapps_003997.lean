-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def every (lst: List α) (n: Nat := 1) (start: Nat := 0) : List α := sorry

theorem every_is_subset {α : Type} (lst : List α) (n: Nat) (start: Nat) 
  (h: start < lst.length) :
  ∀ x ∈ every lst n start, x ∈ lst := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem every_indices_pattern {α : Type} (lst : List α) (n: Nat) (start: Nat)
  (h: start < lst.length) (x : α) (i : Nat) (hi: i < lst.length) :
  x ∈ every lst n start → 
  lst.get ⟨i, hi⟩ = x →
  (i - start) % n = 0 := sorry

theorem every_default_start {α : Type} (lst : List α) (n: Nat) :
  every lst n = every lst n 0 := sorry

theorem every_one_full_slice {α : Type} (lst : List α) (start: Nat)
  (h: 0 < lst.length) :
  every lst 1 start = lst.drop start := sorry
-- </vc-theorems>