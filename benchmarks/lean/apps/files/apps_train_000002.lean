-- <vc-helpers>
-- </vc-helpers>

def solve_sequence (n : Nat) (a b c : List Nat) : List Nat :=
  sorry

theorem solve_sequence_length {n : Nat} {a b c : List Nat} 
  (h1 : n ≥ 2)
  (h2 : a.length = n)
  (h3 : b.length = n) 
  (h4 : c.length = n)
  (h5 : ∀ i, i < n → a[i]! = 1)
  (h6 : ∀ i, i < n → b[i]! = 2)
  (h7 : ∀ i, i < n → c[i]! = 3) :
  (solve_sequence n a b c).length = n := sorry

theorem solve_sequence_elements {n : Nat} {a b c : List Nat}
  (h1 : n ≥ 2)
  (h2 : a.length = n)
  (h3 : b.length = n)
  (h4 : c.length = n)
  (h5 : ∀ i, i < n → a[i]! = 1)
  (h6 : ∀ i, i < n → b[i]! = 2)
  (h7 : ∀ i, i < n → c[i]! = 3) :
  ∀ i, i < n → (solve_sequence n a b c)[i]! ∈ [1, 2, 3] := sorry

/-
info: n3
-/
-- #guard_msgs in
-- #eval len solve_sequence(n3, a3, b3, c3)

-- Apps difficulty: interview
-- Assurance level: unguarded