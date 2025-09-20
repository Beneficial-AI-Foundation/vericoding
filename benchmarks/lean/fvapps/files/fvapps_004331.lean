-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def decompose : Int → List Nat × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem decompose_result_gt_one (n : Int) :
  let (result, _) := decompose n
  ∀ k ∈ result, k > 1 :=
sorry

theorem decompose_remainder_nonneg (n : Int) :
  let (_, remainder) := decompose n
  remainder ≥ 0 :=
sorry

theorem decompose_recompose (n : Int) :
  let (result, remainder) := decompose n
  let recomposed := remainder + (List.foldl (fun acc (i, k) => acc + (i + 2)^k) 0
    (List.zip (List.range result.length) result))
  recomposed = n :=
sorry

theorem decompose_negative (n : Int) :
  n < 0 →
  decompose n = ([], n) :=
sorry

theorem decompose_small_inputs (n : Int) :
  n = 0 ∨ n = 1 →
  decompose n = ([], n) :=
sorry
-- </vc-theorems>