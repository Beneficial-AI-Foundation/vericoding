-- <vc-helpers>
-- </vc-helpers>

def xbonacci (signature : List Int) (n : Nat) : List Int :=
  sorry

theorem xbonacci_length (signature : List Int) (n : Nat) :
  (xbonacci signature n).length = n :=
  sorry

theorem xbonacci_prefix (signature : List Int) (n : Nat) :
  let x := signature.length
  let prefix_len := min n x
  (xbonacci signature n).take prefix_len = signature.take n :=
  sorry

theorem xbonacci_sum_rule (signature : List Int) (n : Nat) (i : Nat) 
    (h1 : n > signature.length) (h2 : i ≥ signature.length) (h3 : i < n) :
  ((xbonacci signature n).get ⟨i, by {
    rw [xbonacci_length]
    exact h3
  }⟩) = 
  (((xbonacci signature n).drop (i-signature.length)).take signature.length).foldl (· + ·) 0 :=
  sorry

theorem xbonacci_zero_length (signature : List Int) :
  xbonacci signature 0 = [] :=
  sorry

theorem xbonacci_nonnegative (signature : List Int) (n : Nat) :
  signature.all (· ≥ 0) →
  (xbonacci signature n).all (· ≥ 0) :=
  sorry

/-
info: [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]
-/
-- #guard_msgs in
-- #eval xbonacci [0, 1] 10

/-
info: [0, 0, 0, 0, 1, 1, 2, 4, 8, 16]
-/
-- #guard_msgs in
-- #eval xbonacci [0, 0, 0, 0, 1] 10

/-
info: []
-/
-- #guard_msgs in
-- #eval xbonacci [1, 2, 3] 0

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible