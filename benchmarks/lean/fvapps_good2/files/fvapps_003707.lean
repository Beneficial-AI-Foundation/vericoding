-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.isDigit : String → Bool :=
  sorry

def missing : String → Int :=
  sorry

def isSequence : String → Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem missing_finds_gap {start : Nat} (h : start ≥ 1 ∧ start ≤ 99) :
  ∀ seq target,
  (∃ curr, curr = start ∧
    seq = String.join (List.map toString (List.range curr)) ∧
    target = curr + 1 ∧
    isSequence (seq.replace (toString target) "")) →
  missing (seq.replace (toString target) "") = target :=
sorry

theorem missing_complete_sequence {start : Nat} (h : start ≥ 1 ∧ start ≤ 999) :
  ∀ seq,
  (∃ curr, curr = start ∧
    seq = String.join (List.map toString (List.range curr)) ∧
    isSequence seq) →
  missing seq = -1 :=
sorry
-- </vc-theorems>