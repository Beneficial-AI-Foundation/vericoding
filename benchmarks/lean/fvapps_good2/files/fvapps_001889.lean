-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sort (l : List α) (f : α → α → Bool) : List α :=
  sorry

def custom_sort_string (s t : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_preserved {s t : String} (h : s.length > 0) :
  (custom_sort_string s t).length = t.length :=
sorry

theorem chars_preserved {s t : String} (h : s.length > 0) :
  List.sort (custom_sort_string s t).data (· ≤ ·) = List.sort t.data (· ≤ ·) :=
sorry

theorem single_char_pattern {s t : String} (h1 : s.length = 1) (h2 : t.length > 0) :
  s.get 0 ∈ t.data →
  (custom_sort_string s t).startsWith (String.mk (List.replicate (t.data.count (s.get 0)) (s.get 0))) :=
sorry

theorem idempotent {s t : String} (h : s.length > 0) :
  custom_sort_string s (custom_sort_string s t) = custom_sort_string s t :=
sorry
-- </vc-theorems>