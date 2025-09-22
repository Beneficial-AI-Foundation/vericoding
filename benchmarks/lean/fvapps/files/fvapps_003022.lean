-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def trotter (n: Int) : Int :=
sorry

def isInsomnia (n: Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem trotter_positive_multiple {n : Int} (h : n > 0) :
  ∃ k : Int, trotter n = n * k ∧ k > 0 :=
sorry

theorem trotter_zero :
  isInsomnia (trotter 0) = true :=
sorry

theorem trotter_nonzero {n : Int} (h : n > 0) :
  trotter n > 0 :=
sorry

theorem trotter_grows {n : Int} (h : n > 0) :
  trotter n ≥ n :=
sorry
-- </vc-theorems>