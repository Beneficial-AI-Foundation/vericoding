-- <vc-preamble>
def almostIncreasingSequence (seq : List Int) : Bool := sorry

def countDescendingPairs (seq : List Int) : Nat := sorry

def isStrictlyIncreasing (seq : List Int) : Bool := sorry

theorem strictly_increasing_always_true {seq : List Int} :
  isStrictlyIncreasing seq → almostIncreasingSequence seq := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countDuplicates (seq : List Int) : Nat := sorry 

theorem duplicate_elements_property {seq : List Int} :
  countDuplicates seq > 1 → ¬almostIncreasingSequence seq := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem too_many_drops_always_false {seq : List Int} :
  countDescendingPairs seq > 1 → ¬almostIncreasingSequence seq := sorry

theorem single_removal_property {seq : List Int} (i : Nat) (h : i < seq.length) :
  isStrictlyIncreasing (seq.take i ++ seq.drop (i+1)) → 
  almostIncreasingSequence seq := sorry

theorem single_element_always_true {seq : List Int} :
  seq.length = 1 → almostIncreasingSequence seq := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval almost_increasing_sequence [1, 3, 2, 1]

/-
info: True
-/
-- #guard_msgs in
-- #eval almost_increasing_sequence [1, 3, 2]

/-
info: True
-/
-- #guard_msgs in
-- #eval almost_increasing_sequence [1, 2, 3]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded