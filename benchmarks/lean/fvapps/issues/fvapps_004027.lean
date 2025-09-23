-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def DIGITS : List Char := sorry

def base64_to_base10 (s : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem base64_to_base10_nonnegative (s: String) 
  (h: s.length > 0)
  (h2: ∀ c ∈ s.data, c ∈ DIGITS) :
  base64_to_base10 s ≥ 0 := sorry

theorem base64_to_base10_longer_is_larger (s: String)
  (h: s.length > 1)
  (h2: ∀ c ∈ s.data, c ∈ DIGITS) :
  base64_to_base10 s > base64_to_base10 (String.dropRight s 1) := sorry

theorem base64_to_base10_matches_manual (s: String)
  (h: s.length > 0)
  (h2: ∀ c ∈ s.data, c ∈ DIGITS) :
  base64_to_base10 s = 
    (List.enum s.data.reverse).foldl
      (fun acc (i, c) => acc + (DIGITS.findIdx? (· = c)).get! * (64 ^ i)) 0 := sorry

theorem base64_to_base10_type (s: String)
  (h: s.length > 0)
  (h2: ∀ c ∈ s.data, c ∈ DIGITS) :
  base64_to_base10 s ≥ 0 := sorry
-- </vc-theorems>