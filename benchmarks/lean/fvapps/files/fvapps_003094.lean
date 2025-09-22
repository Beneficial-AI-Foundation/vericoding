-- <vc-preamble>
def countChar (s : String) (c : Char) : Nat :=
  s.toList.filter (· = c) |>.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def only_duplicates (s : String) : String := sorry

theorem only_duplicates_contains_multiple_occurrences 
  (s : String) (c : Char) : 
  c ∈ (only_duplicates s).data → 
  countChar s c > 1 := 
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem only_duplicates_is_substring
  (s : String) (c : Char) :
  c ∈ (only_duplicates s).data →
  c ∈ s.data := 
sorry

theorem only_duplicates_length
  (s : String) :
  (only_duplicates s).length ≤ s.length :=
sorry

theorem only_duplicates_empty
  (s : String) :
  s = "" → only_duplicates s = "" :=
sorry

theorem only_duplicates_unique_chars
  (s : String) :
  (∀ c, countChar s c ≤ 1) →
  only_duplicates s = "" :=
sorry
-- </vc-theorems>