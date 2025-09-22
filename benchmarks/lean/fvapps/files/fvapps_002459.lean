-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_str_special (s : String) : String :=
  sorry

def isDigit (c : Char) : Bool :=
  sorry

def isLower (c : Char) : Bool :=
  sorry

def isUpper (c : Char) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_str_preserves_length (s : String) :
  String.length (sort_str_special s) = String.length s := by
  sorry

theorem sort_str_preserves_chars (s : String) :
  String.toList (sort_str_special s) = String.toList s := by
  sorry

theorem digits_ordered_by_parity_and_value (s : String) (i j : String.Pos)
    (h1 : i.1 < String.length (sort_str_special s))
    (h2 : j.1 < String.length (sort_str_special s))
    (h3 : i.1 < j.1)
    (hd1 : isDigit ((sort_str_special s).get i))
    (hd2 : isDigit ((sort_str_special s).get j)) :
    let d1 := (sort_str_special s).get i
    let d2 := (sort_str_special s).get j
    (d1.toNat % 2 = 0 → d2.toNat % 2 ≠ 1) ∧
    (d1.toNat % 2 = d2.toNat % 2 → d1.toNat ≤ d2.toNat) := by
  sorry

theorem letters_ordered_by_case_and_value (s : String) (i j : String.Pos)
    (h1 : i.1 < String.length (sort_str_special s))
    (h2 : j.1 < String.length (sort_str_special s))
    (h3 : i.1 < j.1)
    (hl1 : (isLower ((sort_str_special s).get i) ∨ isUpper ((sort_str_special s).get i)))
    (hl2 : (isLower ((sort_str_special s).get j) ∨ isUpper ((sort_str_special s).get j))) :
    let c1 := (sort_str_special s).get i
    let c2 := (sort_str_special s).get j
    (isUpper c1 → ¬isLower c2) ∧
    ((isUpper c1 = isUpper c2) → c1 ≤ c2) := by
  sorry
-- </vc-theorems>