-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_feelings (input : String) (feelings : List String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_feelings_bounds
  {input : String}
  {feelings : List String}
  (h1 : input.length > 0)
  (h2 : feelings ≠ [])
  : let result := count_feelings input feelings
    let count := String.toNat! (result.take (result.length - (if result.startsWith "1 " then 9 else 10)))
    count ≥ 0 ∧ count ≤ feelings.length :=
  sorry

theorem count_feelings_exact_match
  {feeling : String}
  (h : feeling.length > 0)
  : count_feelings feeling [feeling] = "1 feeling." :=
  sorry
-- </vc-theorems>