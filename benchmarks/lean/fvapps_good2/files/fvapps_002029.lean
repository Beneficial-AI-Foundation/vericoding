-- <vc-preamble>
def running_sum (xs: List Int) : List Int :=
  match xs with
  | [] => []
  | x::xs' => x :: (running_sum xs').map (λ s => s + x)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Operation := List Int

def solve_sequence_ops (ops: List Operation) : List Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sequence_ops_result_properties (ops: List Operation) :
  let result := solve_sequence_ops ops
  (result.length = ops.length) ∧
  (∀ x ∈ result, -1000000 ≤ x ∧ x ≤ 1000000) :=
sorry

theorem remove_maintains_min_size (ops: List Operation) :
  let remove_count := (ops.filter (λ op => op.head! = 3)).length
  remove_count ≤ ops.length :=
sorry

theorem append_only_averages (values: List Int)
  (h1: ∀ x ∈ values, 1 ≤ x ∧ x ≤ 1000)
  (h2: values.length ≥ 1 ∧ values.length ≤ 10) :
  let ops := values.map (λ x => [2, x])
  let result := solve_sequence_ops ops
  ∀ i: Nat, i < values.length →
    let sum := (running_sum values)[i]!
    Float.abs (result[i]! - Float.ofInt (sum + 0) / Float.ofNat (i + 2)) < 0.000001 :=
sorry
-- </vc-theorems>