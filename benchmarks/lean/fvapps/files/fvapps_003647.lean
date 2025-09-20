-- <vc-preamble>
def HashMap (α β : Type) := List (α × β)

variable (input: HashMap String (List Char))
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_words (input: HashMap String (List Char)) : List String := sorry

def IsSorted (l: List String) : Prop :=
  ∀ i j, i < j → j < l.length → (l.get ⟨i, by sorry⟩) ≤ (l.get ⟨j, by sorry⟩)

-- Words returned are sorted
-- </vc-definitions>

-- <vc-theorems>
theorem words_are_sorted : IsSorted (get_words input) := sorry

-- All words have the same length

theorem words_same_length
  (w1 w2: String)
  (hw1: w1 ∈ get_words input)
  (hw2: w2 ∈ get_words input)
  : w1.length = w2.length := sorry

-- All words are permutations of each other

theorem words_are_permutations
  (w1 w2: String)
  (hw1: w1 ∈ get_words input)
  (hw2: w2 ∈ get_words input)
  : ∃ (perm: List Char), w2.data = perm ∧ perm.length = w1.data.length := sorry
-- </vc-theorems>