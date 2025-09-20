-- <vc-preamble>
def max (a b : Int) : Int :=
if a ≥ b then a else b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_special_segment_sum (n: Nat) (a b: List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_special_segment_sum_geq_max_a {n: Nat} {a b: List Int} 
  (hn: n ≥ 2) (ha: a.length = n) (hb: b.length = n) :
  max_special_segment_sum n a b ≥ a.foldl max 0 :=
sorry

theorem max_special_segment_sum_monotonic {n: Nat} {a b: List Int} 
  (hn: n ≥ 2) (ha: a.length = n) (hb: b.length = n)
  (hb_nonneg: ∀ x ∈ b, x ≥ 0) :
  let a_increased := a.map (· + 1)
  max_special_segment_sum n a_increased b ≥ max_special_segment_sum n a b :=
sorry

theorem zero_b_equals_max_a {n: Nat} {a: List Int} 
  (hn: n ≥ 2) (ha: a.length = n)
  (h_pos: ∀ x ∈ a, x > 0) :
  let b := List.replicate n (0:Int)
  max_special_segment_sum n a b ≥ a.foldl max 0 :=
sorry
-- </vc-theorems>