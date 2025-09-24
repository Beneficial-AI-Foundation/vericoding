-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_string_similarity (s : String) : Nat :=
  if s.length = 0 then panic! "Empty string not allowed"
  else sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_string_similarity_non_negative {s : String} (h : s.length > 0) : 
  solve_string_similarity s ≥ 0 := by sorry

theorem solve_string_similarity_bounded {s : String} (h : s.length > 0) :
  solve_string_similarity s < 10^9 + 7 := by sorry

theorem single_char_string {s : String} (h1 : s.length = 1) :
  solve_string_similarity s = 0 := by sorry

theorem same_char_string {s : String} (h1 : s.length > 0) 
  (h2 : ∀ (i j : String.Pos), s.get i = s.get j) :
  solve_string_similarity s = 0 := by sorry

theorem repeated_char_string (n : Nat) (h : n > 0) :
  solve_string_similarity (String.mk (List.replicate n 'a')) = 0 := by sorry

theorem alternating_string_bounded (n : Nat) (h : 0 < n) :
  let s := String.mk (List.join (List.replicate n ['a', 'b']))
  0 ≤ solve_string_similarity s ∧ solve_string_similarity s < 10^9 + 7 := by sorry

theorem unique_chars_bounded (n : Nat) (h : 0 < n) :
  let s := String.mk (List.map (fun i => Char.ofNat (Char.toNat 'a' + i)) (List.range n))
  0 ≤ solve_string_similarity s ∧ solve_string_similarity s < 10^9 + 7 := by sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_string_similarity "z"

/-
info: 144
-/
-- #guard_msgs in
-- #eval solve_string_similarity "abcd"

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_string_similarity "aaaa"
-- </vc-theorems>