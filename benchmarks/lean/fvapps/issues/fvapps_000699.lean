-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pattern_sequence (k: Nat) : String := sorry

def parseInts (s: String) : List Int := 
  (s.splitOn " ").filterMap String.toInt?
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_sequence_line_count {k: Nat} (hk: k > 0) :
  ((pattern_sequence k).splitOn "\n").length = k := sorry

theorem pattern_sequence_numbers_per_line {k: Nat} (hk: k > 0) :
  let lines := (pattern_sequence k).splitOn "\n"
  ∀ i : Nat, i < lines.length → 
  ((lines[i]!).splitOn " ").length = i.succ := sorry

theorem pattern_sequence_valid_ints {k: Nat} (hk: k > 0) :
  let lines := (pattern_sequence k).splitOn "\n"
  ∀ line ∈ lines,
  ∀ num ∈ line.splitOn " ",
  String.toInt? num ≠ none := sorry

theorem pattern_sequence_fibonacci {k: Nat} (hk: k > 0) :
  let lines := (pattern_sequence k).splitOn "\n"
  let nums := lines.bind (λ line => parseInts line)
  ∀ i, i ≥ 2 → i < nums.length →
    nums[i]! = nums[i-1]! + nums[i-2]! := sorry

/-
info: '0'
-/
-- #guard_msgs in
-- #eval pattern_sequence 1

/-
info: expected
-/
-- #guard_msgs in
-- #eval pattern_sequence 2

/-
info: expected
-/
-- #guard_msgs in
-- #eval pattern_sequence 3
-- </vc-theorems>