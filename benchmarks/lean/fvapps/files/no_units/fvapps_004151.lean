-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def combine_names (first last : String) : String := sorry

theorem combine_names_type (first last : String) :
  first.length > 0 → last.length > 0 →
  combine_names first last = combine_names first last :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem combine_names_starts_ends (first last : String) :
  first.length > 0 → last.length > 0 →
  String.startsWith (combine_names first last) first ∧
  String.endsWith (combine_names first last) last :=
sorry

theorem combine_names_space_count (first last : String) :
  first.length > 0 → last.length > 0 →
  String.length (String.replace (combine_names first last) " " "") + 1 = 
  String.length (combine_names first last) :=
sorry

theorem combine_names_length (first last : String) :
  first.length > 0 → last.length > 0 →
  String.length (combine_names first last) = String.length first + String.length last + 1 :=
sorry
-- </vc-theorems>