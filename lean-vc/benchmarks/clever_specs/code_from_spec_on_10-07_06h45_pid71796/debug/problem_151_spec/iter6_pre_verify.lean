def problem_spec
-- function signature
(impl: List Rat → Int)
-- inputs
(numbers: List Rat) :=
let isEven (n : Rat) := n % 2 = 0;
let isNegative (n : Rat) := n < 0;
let isNotInteger (n : Rat) := ¬ n.isInt;
-- spec
let spec (result: Int) :=
0 < numbers.length →
0 ≤ result ∧
if numbers.length = 1
then result = if (isEven numbers[0]! ∨ isNegative numbers[0]! ∨ isNotInteger numbers[0]!) then (0 : Int) else numbers[0]!.floor ^ 2
else result = if (isEven numbers[0]! ∨ isNegative numbers[0]! ∨ isNotInteger numbers[0]!) then (0 : Int) else numbers[0]!.floor ^ 2 + impl numbers.tail
-- program terminates
∃ result, impl numbers = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def isEven (n : Rat) : Prop := (n.floor : Int) % 2 = 0

-- LLM HELPER
def isNegative (n : Rat) : Prop := n < (0 : Rat)

-- LLM HELPER
def isNotInteger (n : Rat) : Prop := ¬ n.isInt

-- LLM HELPER
instance : DecidablePred isEven := fun n => Int.decidable_dvd_iff

-- LLM HELPER
instance : DecidablePred isNegative := fun n => by
  apply @decidable_of_iff _ _ (Rat.decidableLT n 0)
  rfl

-- LLM HELPER
instance : DecidablePred isNotInteger := fun n => by
  apply @decidable_of_iff _ _ (decidable_of_decidable_of_iff (Rat.decidable_isInt n) (by rfl))
  rfl

def implementation (numbers: List Rat) : Int := 
  match numbers with
  | [] => 0
  | [x] => if (isEven x ∨ isNegative x ∨ isNotInteger x) then 0 else x.floor ^ 2
  | x :: xs => if (isEven x ∨ isNegative x ∨ isNotInteger x) then 0 else x.floor ^ 2 + implementation xs

-- LLM HELPER
lemma implementation_nonneg (numbers: List Rat) : 0 ≤ implementation numbers := by
  induction numbers with
  | nil => simp [implementation]
  | cons x xs ih =>
    simp [implementation]
    split_ifs with h
    · simp
    · apply Int.add_nonneg
      · apply Int.sq_nonneg
      · exact ih

-- LLM HELPER
lemma implementation_single (x: Rat) : 
  implementation [x] = if (isEven x ∨ isNegative x ∨ isNotInteger x) then 0 else x.floor ^ 2 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_cons (x: Rat) (xs: List Rat) (h: xs ≠ []) :
  implementation (x :: xs) = if (isEven x ∨ isNegative x ∨ isNotInteger x) then 0 else x.floor ^ 2 + implementation xs := by
  simp [implementation]

-- LLM HELPER
lemma spec_equiv (numbers: List Rat) (h: 0 < numbers.length) : 
  let isEven_local (n : Rat) := n % 2 = (0 : Rat)
  let isNegative_local (n : Rat) := n < (0 : Rat)
  let isNotInteger_local (n : Rat) := ¬ n.isInt
  (isEven_local numbers[0]! ∨ isNegative_local numbers[0]! ∨ isNotInteger_local numbers[0]!) = 
  (isEven numbers[0]! ∨ isNegative numbers[0]! ∨ isNotInteger numbers[0]!) := by
  simp [isEven, isNegative, isNotInteger]
  congr 1
  · rw [← Rat.floor_mod_two_eq_iff]
    rfl
  · rfl
  · rfl

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  · intro h_len_pos
    constructor
    · exact implementation_nonneg numbers
    · cases' numbers with x xs
      · simp at h_len_pos
      · cases' xs with y ys
        · simp [implementation_single]
          rw [spec_equiv]
          exact h_len_pos
        · simp [List.length] at h_len_pos
          simp [implementation_cons]
          simp [List.tail]
          rw [spec_equiv]
          exact h_len_pos