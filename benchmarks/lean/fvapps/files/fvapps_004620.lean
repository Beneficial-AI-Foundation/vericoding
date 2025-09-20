-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_hexagon_beam (n: Nat) (seq: List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_hexagon_beam_nonnegative {n: Nat} {seq: List Int}
  (hseq : seq.length > 0)
  (hseqnonneg : ∀ x ∈ seq, x ≥ 0) :
  max_hexagon_beam n seq ≥ 0 := sorry
-- </vc-theorems>