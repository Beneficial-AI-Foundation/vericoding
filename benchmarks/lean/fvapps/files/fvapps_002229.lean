-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_shortest_string_length (s : String) : Nat := sorry

theorem shortest_length_non_negative (s : String) : 
  get_shortest_string_length s ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem shortest_length_at_most_input (s : String) :
  get_shortest_string_length s ≤ String.length s := sorry

theorem AB_reduces_length (s : String) (i : Nat) :
  i + 1 < s.length →
  (h1 : i < s.length) →
  (h2 : i + 1 < s.length) →
  s.data[i]'h1 = 'A' →
  s.data[i + 1]'h2 = 'B' →
  get_shortest_string_length s < String.length s := sorry

theorem BB_reduces_length (s : String) (i : Nat) :
  i + 1 < s.length →
  (h1 : i < s.length) →
  (h2 : i + 1 < s.length) →
  s.data[i]'h1 = 'B' →
  s.data[i + 1]'h2 = 'B' →
  get_shortest_string_length s < String.length s := sorry

theorem repeated_B_reduces_to_zero_or_one (n : Nat) :
  let s := String.mk (List.replicate n 'B')
  get_shortest_string_length s = 0 ∨ get_shortest_string_length s = 1 := sorry
-- </vc-theorems>