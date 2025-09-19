-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def correct (m n : Nat) (bits : String) : String := sorry

theorem output_length_matches_input 
  (m n : Nat)
  (bits : String)
  (h1 : m > 0)
  (h2 : n > 0)
  (h3 : bits.length = m*n + m + n) :
  (correct m n bits).length = bits.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_differs_by_at_most_one_bit
  (m n : Nat) 
  (bits : String)
  (h1 : m > 0)
  (h2 : n > 0)
  (h3 : bits.length = m*n + m + n) :
  let result := correct m n bits
  let diffs := (List.zip bits.data result.data).filter (fun p => p.1 ≠ p.2)
  diffs.length ≤ 1 := sorry
-- </vc-theorems>