-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dedupe_sort_string (s : String) : String := sorry
def print_string_combinations (s : String) (k : Nat) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem test_k_equals_one {s : String} (h : s ≠ "") :
  let deduped := dedupe_sort_string s
  let result := print_string_combinations deduped 1
  let lines := result.splitOn "\n"
  lines = (s.data.eraseDups).map toString := sorry

theorem test_dedupe_properties {s : String} (h₁ : s.all Char.isUpper) (h₂ : s.length ≤ 5) (h₃ : s ≠ "") :
  let deduped := dedupe_sort_string s
  deduped.data = deduped.data.eraseDups := sorry
-- </vc-theorems>