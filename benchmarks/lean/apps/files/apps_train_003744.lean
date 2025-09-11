-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def decipher_message (s : String) : String := sorry

theorem decipher_preserves_length (s : String) (h : s.length > 0) :
  (decipher_message s).length = s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem decipher_preserves_chars (s : String) (h : s.length > 0) :
  ∀ c, (c ∈ (decipher_message s).data ↔ c ∈ s.data) := sorry

theorem decipher_idempotent (s : String) (h : s.length > 0) 
  (h2 : ∃ n : Nat, n * n = s.length) :
  decipher_message (decipher_message s) = s := sorry

theorem decipher_small_strings (s : String) (h : s.length ≤ 1) :
  decipher_message s = s := sorry

theorem decipher_perfect_squares (n : Nat) (h : n > 0) (h2 : n ≤ 10) :
  let s := String.mk (List.replicate (n*n) 'x')
  (decipher_message s).length = n*n ∧
  (decipher_message s).data.all (· = 'x') := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval decipher_message "ArNran u rstm5twob  e ePb"

/-
info: expected2
-/
-- #guard_msgs in
-- #eval decipher_message "92287a76 585a2y0"

/-
info: expected3
-/
-- #guard_msgs in
-- #eval decipher_message "796820 2 "
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded