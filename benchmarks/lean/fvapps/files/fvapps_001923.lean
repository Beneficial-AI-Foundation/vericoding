-- <vc-preamble>
def abs (n : Nat) (m : Nat) : Nat :=
  if n ≥ m then n - m else m - n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_median_smoothing (n : Nat) (seq : List Nat) : Nat × Option (List Nat) :=
  sorry

def is_sorted_window (arr : List Nat) (i : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem median_smoothing_properties
  (n : Nat) (seq : List Nat)
  (h1 : n ≥ 2)
  (h2 : ∀ x ∈ seq, x ≤ 1)
  (steps : Nat) (result : Option (List Nat)) :
  let (steps', result') := solve_median_smoothing n seq
  match result' with
  | none => steps' < 0
  | some res =>
    steps' ≥ 0 ∧
    res.length = n ∧
    (∀ i, 0 < i → i < res.length - 1 → is_sorted_window res i) ∧
    (seq.length > 0 → res.length > 0 → List.head! res = List.head! seq) ∧
    (seq.length > 0 → res.length > 0 → List.getLast res (by sorry) = List.getLast seq (by sorry))
  :=
sorry

theorem constant_sequence_property
  (n : Nat) (seq : List Nat)
  (h1 : n ≥ 2)
  (h2 : ∀ x ∈ seq, x = 0) :
  let (steps, result) := solve_median_smoothing n seq
  steps = 0 ∧ result = some seq :=
sorry

theorem alternating_sequence_property
  (n : Nat)
  (h : n ≥ 3) :
  let seq := List.map (fun i => i % 2) (List.range n)
  let (steps, result) := solve_median_smoothing n seq
  steps ≥ 0 ∧
  match result with
  | none => False
  | some res =>
    ∀ i, i + 1 < res.length →
    abs (List.get! res i) (List.get! res (i+1)) ≤ 1
  :=
sorry
-- </vc-theorems>