-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def threshold (thres : Int) (seq : Array Int) : Array Int × Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem threshold_spec (thres : Int) (seq : Array Int) :
let (seq1, seq2) := threshold thres seq
(∀ x, x ∈ seq1 → x ≤ thres) ∧
(∀ x, x ∈ seq2 → x ≥ thres) ∧
(seq1.size + seq2.size = seq.size) :=
sorry
-- </vc-theorems>