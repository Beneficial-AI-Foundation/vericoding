-- <vc-preamble>
def maximum (xs : List Int) : Int := xs.foldl max 0

def sum (xs : List Int) : Int := xs.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_sum (arr : List Int) : Int := sorry

def solve (arr : List Int) (k : Nat) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_vs_max_sum (arr : List Int) (k : Nat) (h : arr ≠ []) (hk : k > 0) :
  solve arr k ≥ max_sum arr := sorry

theorem solve_monotonic_k (arr : List Int) (k : Nat) (h : arr ≠ []) (hk : k > 1) :
  solve arr k ≥ solve arr 1 := sorry

theorem solve_k1_equals_maxsum (arr : List Int) (h : arr ≠ []) :
  solve arr 1 = max_sum arr := sorry

theorem solve_concatenation (arr : List Int) (h : arr ≠ []) :
  solve arr 2 ≥ max_sum (arr ++ arr) := sorry
-- </vc-theorems>