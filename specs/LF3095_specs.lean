-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_pow_dig_seq (num exp k : Nat) : Nat × List Nat × Nat × Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_pow_dig_seq_result_structure 
  (num exp k : Nat)
  (h1 : num > 0)
  (h2 : num ≤ 100000)
  (h3 : exp > 0)
  (h4 : exp ≤ 5)
  (h5 : k > 0)
  (h6 : k ≤ 100) :
  let result := sum_pow_dig_seq num exp k
  result.1 ≥ 0 ∧ 
  result.2.2.1 = result.2.1.length ∧
  (result.2.1 ≠ [] → 
    (List.elem result.2.2.2 result.2.1 ∧
     result.1 + result.2.2.1 ≤ k ∧
     ∀ (x y : Nat), List.elem x result.2.1 → List.elem y result.2.1 → x = y → x = y)) :=
  sorry

theorem sum_pow_dig_seq_consistent
  (num exp : Nat)
  (h1 : num > 0)
  (h2 : num ≤ 1000)
  (h3 : exp > 0)
  (h4 : exp ≤ 3) :
  let r1 := sum_pow_dig_seq num exp 100
  let r2 := sum_pow_dig_seq num exp 200
  r1.2.1 ≠ [] →
    (r1.2.1 = r2.2.1 ∧
     r1.1 = r2.1 ∧
     r1.2.2.1 = r2.2.2.1) :=
  sorry

theorem sum_pow_dig_seq_power_one
  (num : Nat)
  (h1 : num > 0)
  (h2 : num ≤ 1000) :
  let result := sum_pow_dig_seq num 1 20
  result.2.1 ≠ [] →
    ∀ x, List.elem x result.2.1 → x < 10 :=
  sorry
-- </vc-theorems>