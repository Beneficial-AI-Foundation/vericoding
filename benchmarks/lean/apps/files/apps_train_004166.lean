-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def freq_seq (s : String) (sep : String) : String := sorry 

def String.count (s : String) (c : Char) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem freq_seq_length {s sep : String} (h1 : s.length > 0) (h2 : sep.length = 1) :
  (freq_seq s sep).length > 0 := sorry

theorem freq_seq_counts {s sep : String} (h1 : s.length > 0) (h2 : sep.length = 1) 
  (i : Nat) (hi : i < s.length) :
  let c := s.data[i]
  s.count c > 0 := sorry

theorem freq_seq_nonneg {s sep : String} (h1 : s.length > 0) (h2 : sep.length = 1) :
  ∀ c : Char, c ∈ s.data → s.count c ≥ 0 := sorry

theorem freq_seq_deterministic {s sep : String} (h1 : s.length > 0) (h2 : sep.length = 1) :
  freq_seq s sep = freq_seq s sep := sorry

/-
info: '1-1-3-3-2-1-1-2-1-3-1'
-/
-- #guard_msgs in
-- #eval freq_seq "hello world" "-"

/-
info: '1:7:7:7:7:7:7:7'
-/
-- #guard_msgs in
-- #eval freq_seq "19999999" ":"

/-
info: '3x3x3x2x2x1'
-/
-- #guard_msgs in
-- #eval freq_seq "^^^**$" "x"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded