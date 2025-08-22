def problem_spec
-- function signature
(impl: List Rat → List Rat → List Rat)
-- inputs
(scores guesses: List Rat) :=
-- spec
let spec (result: List Rat) :=
  result.length = scores.length ∧
  scores.length = guesses.length ∧
  ∀ i, i < scores.length →
  if scores[i]! > guesses[i]! then result[i]! + guesses[i]! = scores[i]!
  else result[i]! + scores[i]! = guesses[i]!
-- program terminates
∃ result, impl scores guesses = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
instance : Inhabited Rat := ⟨0⟩

-- LLM HELPER
instance : OfNat Rat 0 := ⟨(0 : Int)⟩

-- LLM HELPER
instance : OfNat Rat 1 := ⟨(1 : Int)⟩

-- LLM HELPER
instance : DecidableRel (· > · : Rat → Rat → Prop) := fun a b => Rat.decLt b a

-- LLM HELPER
def compute_diff (s g: Rat) : Rat :=
  if s > g then s - g else g - s

def implementation (scores guesses: List Rat) : List Rat := 
  List.zipWith compute_diff scores guesses

-- LLM HELPER
lemma zipWith_length (f: Rat → Rat → Rat) (l1 l2: List Rat) : 
  (List.zipWith f l1 l2).length = min l1.length l2.length := by
  induction l1, l2 using List.zipWith.induction f
  · simp
  · simp
  · simp
  · simp [List.zipWith_cons_cons, *]

-- LLM HELPER
lemma zipWith_get (f: Rat → Rat → Rat) (l1 l2: List Rat) (i: Nat) 
  (h1: i < l1.length) (h2: i < l2.length) :
  (List.zipWith f l1 l2)[i]! = f l1[i]! l2[i]! := by
  induction l1, l2 using List.zipWith.induction f generalizing i
  · simp at h1
  · simp at h1
  · simp at h2
  · case cons_cons a l1 b l2 ih =>
    cases i with
    | zero => simp [List.zipWith_cons_cons]
    | succ i' => 
      simp [List.zipWith_cons_cons, List.get_cons_succ]
      apply ih
      · simp at h1; exact h1
      · simp at h2; exact h2

-- LLM HELPER
lemma compute_diff_property (s g: Rat) :
  if s > g then compute_diff s g + g = s
  else compute_diff s g + s = g := by
  simp [compute_diff]
  split
  · simp [Rat.sub_add_cancel]
  · simp [Rat.add_sub_cancel]

theorem correctness
(scores guesses: List Rat)
: problem_spec implementation scores guesses := by
  simp [problem_spec, implementation]
  use List.zipWith compute_diff scores guesses
  constructor
  · rfl
  · constructor
    · simp [zipWith_length]
    · constructor
      · simp
      · intro i hi
        have h1: i < scores.length := by
          simp at hi
          exact hi
        have h2: i < guesses.length := by
          simp at hi
          exact hi
        rw [zipWith_get compute_diff scores guesses i h1 h2]
        exact compute_diff_property scores[i]! guesses[i]!