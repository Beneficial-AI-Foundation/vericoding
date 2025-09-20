-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pillow (strings: List String) : Bool := sorry

theorem pillow_vertical_alignment (strings: List String) (h: strings.length = 2) :
  pillow strings = (∃ i, i < (strings[0]!).length ∧ 
                        (strings[0]!).data[i]? = some 'n' ∧ 
                        (strings[1]!).data[i]? = some 'B') := sorry

theorem pillow_same_length (s1 s2: String) :
  let minLen := min s1.length s2.length
  let strings := [s1.take minLen, s2.take minLen]
  pillow strings = true ∨ pillow strings = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pillow_identical_strings (s: String) :
  pillow [s, s] = false := sorry

theorem pillow_minimal_case :
  pillow ["n", "B"] = true := sorry

theorem pillow_empty_strings :
  pillow ["", ""] = false := sorry
-- </vc-theorems>