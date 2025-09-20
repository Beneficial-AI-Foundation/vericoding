-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_good_substrings (s : String) : Nat :=
  sorry

@[simp]
-- </vc-definitions>

-- <vc-theorems>
theorem count_good_substrings_nonnegative (s : String) :
  count_good_substrings s ≥ 0 := sorry

theorem single_char_has_no_good_substrings (c : Char) :
  count_good_substrings (String.mk [c]) = 0 := sorry

theorem identical_chars_count (n : Nat) (c : Char) :
  let s := String.mk (List.replicate n c)
  count_good_substrings s = if n > 1 then n * (n-1) / 2 else 0 := sorry

theorem alternating_chars_pattern_count {s : String} :
  count_good_substrings s ≥ 
    (List.range s.length).foldl (fun acc i =>
      if i + 2 < s.length && s.data[i]! = s.data[i+2]! && 
         s.data[i+1]! ≠ s.data[i]!
      then acc + 1
      else acc) 0 := sorry
-- </vc-theorems>