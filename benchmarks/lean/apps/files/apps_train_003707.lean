-- <vc-preamble>
def String.isDigit : String → Bool :=
  sorry

def missing : String → Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/- For a complete sequence with no gaps, missing returns -1 -/

theorem missing_complete_sequence {start : Nat} (h : start ≥ 1 ∧ start ≤ 999) :
  ∀ seq,
  (∃ curr, curr = start ∧
    seq = String.join (List.map toString (List.range curr)) ∧
    isSequence seq) →
  missing seq = -1 :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval missing "123567"

/-
info: 92
-/
-- #guard_msgs in
-- #eval missing "899091939495"

/-
info: 100
-/
-- #guard_msgs in
-- #eval missing "9899101102"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded