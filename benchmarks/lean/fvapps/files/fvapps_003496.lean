-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Char.isValidUnicode (c : Char) : Bool := sorry

def letterCount (s : String) : Char → Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem letterCount_all_counts_positive {s : String} {c : Char} :
  letterCount s c > 0 → c ∈ s.data := by sorry

theorem letterCount_keys_in_string {s : String} {c : Char} :
  letterCount s c > 0 → c ∈ s.data := by sorry

theorem letterCount_sum_equals_length {s : String} :
  (s.data.foldl (fun acc c => acc + letterCount s c) 0) = s.length := by sorry

theorem letterCount_count_correct {s : String} {c : Char} :
  letterCount s c = (s.data.filter (· = c)).length := by sorry 

theorem letterCount_nonempty_result {s : String} :
  s ≠ "" → ∃ c, letterCount s c > 0 := by sorry

theorem letterCount_valid_chars {s : String} {c : Char} :
  letterCount s c > 0 → Char.isValidUnicode c := by sorry
-- </vc-theorems>