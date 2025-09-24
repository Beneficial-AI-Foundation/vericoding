-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def title_to_number (s : String) : Nat :=
  sorry

def number_to_title (n : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem title_to_number_positive (title : String) :
  title_to_number title > 0 := by
  sorry

theorem title_to_number_monotone (title : String) :
  (title.length > 1) →
  title_to_number title > title_to_number (String.dropRight title 1) := by
  sorry

theorem title_to_number_roundtrip (n : Nat) :
  n > 0 → n ≤ 2^20 →
  title_to_number (number_to_title n) = n := by
  sorry
-- </vc-theorems>