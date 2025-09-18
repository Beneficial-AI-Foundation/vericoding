-- <vc-preamble>
def is_in_middle (s : String) : Bool := sorry

theorem empty_or_short_string (s : String) :
  s.length ≤ 3 → is_in_middle s = false := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def containsSubstring (s₁ s₂ : String) : Bool := sorry

theorem without_abc (s : String) :
  containsSubstring s "abc" = false → is_in_middle s = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem equal_padding (n : Nat) : 
  let s := String.mk (List.replicate n 'A') ++ "abc" ++ String.mk (List.replicate n 'A')
  is_in_middle s = true := sorry
-- </vc-theorems>