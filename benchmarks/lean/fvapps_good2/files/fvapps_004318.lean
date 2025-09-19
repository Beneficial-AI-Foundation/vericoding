-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def string_color (s : String) : Option String :=
sorry

def hexToNat (s : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem string_color_short_strings {s : String} (h : s.length ≤ 1) :
  string_color s = none :=
sorry

theorem string_color_valid_ranges {s : String} (h : s.length ≥ 2) :
  match string_color s with
  | none => False
  | some result =>
    let r := hexToNat result
    let g := hexToNat result
    let b := hexToNat result
    r ≤ 255 ∧ g ≤ 255 ∧ b ≤ 255 :=
sorry

theorem string_color_longer_strings {s : String} (h : s.length ≥ 2) :
  match string_color s with
  | none => False
  | some result =>
    result.length = 6 ∧
    (∀ c ∈ result.data, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F']) :=
sorry

theorem string_color_deterministic {s : String} :
  string_color s = string_color s :=
sorry
-- </vc-theorems>