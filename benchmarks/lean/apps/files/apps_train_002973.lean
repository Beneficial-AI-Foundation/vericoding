-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def string_chunk (s : String) (n : Nat) : List String := sorry

theorem string_chunk_length_property (s : String) (n : Nat) (h : n > 0) :
  s.length > 0 → String.length (String.join (string_chunk s n)) = String.length s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem string_chunk_size_property (s : String) (n : Nat) (h : n > 0) :
  let chunks := string_chunk s n
  chunks.length > 0 →
  (∀ chunk ∈ chunks, chunk.length ≤ n) ∧
  (∀ chunk ∈ chunks.dropLast, chunk.length = n) := sorry

theorem string_chunk_invalid_n (s : String) (n : Nat) :
  n = 0 → string_chunk s n = [] := sorry

theorem string_chunk_reconstructs_original (s : String) (n : Nat) (h : n > 0) :
  String.join (string_chunk s n) = s := sorry

/-
info: ['co', 'de', 'wa', 'rs']
-/
-- #guard_msgs in
-- #eval string_chunk "codewars" 2

/-
info: []
-/
-- #guard_msgs in
-- #eval string_chunk "hello" 0

/-
info: ['hi']
-/
-- #guard_msgs in
-- #eval string_chunk "hi" 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded