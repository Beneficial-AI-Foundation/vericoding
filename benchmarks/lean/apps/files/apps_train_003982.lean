-- <vc-preamble>
def find_missing (seq : List Int) : Int :=
  sorry

def list_range_int (n : Nat) : List Int :=
  (List.range n).map Int.ofNat
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_arithmetic_seq (seq : List Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_missing_complete_sequence
  (start step : Int)
  (length : Nat)
  (h1 : length ≥ 3)
  (h2 : length ≤ 10)
  (h3 : -100 ≤ start)
  (h4 : start ≤ 100)
  (h5 : 1 ≤ step)
  (h6 : step ≤ 20) :
  let full_seq := (list_range_int length).map (fun i => start + i * step)
  let i := length / 2
  let seq_with_missing := (full_seq.take i) ++ (full_seq.drop (i+1))
  find_missing seq_with_missing = (full_seq.get! i) :=
sorry

theorem find_missing_existing_arithmetic
  {seq : List Int}
  (h1 : seq.length ≥ 3)
  (h2 : seq.length ≤ 20)
  (h3 : is_arithmetic_seq seq = true) :
  let diff := seq.get! 1 - seq.get! 0
  ∃ i, i < seq.length - 1 ∧ 
       seq.get! (i+1) - seq.get! i ≠ diff →
       find_missing seq = seq.get! i + diff :=
sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_missing [1, 2, 3, 4, 6, 7, 8, 9]

/-
info: 7
-/
-- #guard_msgs in
-- #eval find_missing [1, 3, 5, 9, 11]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_missing [1, 3, 4]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded