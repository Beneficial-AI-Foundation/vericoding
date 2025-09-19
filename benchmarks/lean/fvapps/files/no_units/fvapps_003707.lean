-- <vc-preamble>
def String.isDigit : String → Bool :=
  sorry

def missing : String → Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSequence : String → Bool :=
  sorry

/- For a sequence with one number removed, missing finds the removed number -/
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
-- </vc-theorems>