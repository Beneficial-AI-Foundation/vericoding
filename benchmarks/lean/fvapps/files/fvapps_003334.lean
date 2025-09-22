-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validate_sequence (seq: List Int) : Bool := sorry

theorem too_short_sequences_invalid (seq: List Int) :
  seq.length ≤ 2 → validate_sequence seq = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arithmetic_sequences_valid
    (start diff: Int) (length: Nat) (h: 0 < length) (h': length ≤ 100) :
  let seq := (List.range (length + 3)).map (fun i => start + (Int.ofNat i) * diff)
  validate_sequence seq = true := sorry

theorem breaking_arithmetic_pattern_invalidates
    (seq: List Int) (position: Nat) (h: 3 ≤ seq.length) (h': 0 < position) :
  validate_sequence seq = true →
  let position' := position % (seq.length - 1)
  let position'' := if position' = 0 then 1 else position'
  let modified_seq := seq.set position'' (seq.get! position'' + 1)
  validate_sequence modified_seq = false := sorry

theorem common_difference_property (start diff: Int) (length: Nat)
    (h: 3 ≤ length) (h': length ≤ 100) :
  let seq := (List.range length).map (fun i => start + (Int.ofNat i) * diff)
  validate_sequence seq = true →
  let diffs := (List.range (length - 1)).map (fun i => seq.get! (i+1) - seq.get! i)
  ∀ i, i < diffs.length → diffs.get! i = diffs.get! 0 := sorry
-- </vc-theorems>