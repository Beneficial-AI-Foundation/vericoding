-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_sheep (n: Int) : String := sorry

theorem count_sheep_format {n: Nat} :
  count_sheep n = String.join (List.map (fun i => s!"{i} sheep...") (List.range n)) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_sheep_count {n: Nat} :
  (count_sheep n).length = n * ("1 sheep...".length) := sorry

theorem count_sheep_ordered {n: Nat} (h: n > 0) :
  count_sheep n ≠ "" := sorry

theorem count_sheep_zero :
  count_sheep 0 = "" := sorry

theorem count_sheep_negative {n: Int} (h: n < 0) :
  count_sheep n = "" := sorry
-- </vc-theorems>