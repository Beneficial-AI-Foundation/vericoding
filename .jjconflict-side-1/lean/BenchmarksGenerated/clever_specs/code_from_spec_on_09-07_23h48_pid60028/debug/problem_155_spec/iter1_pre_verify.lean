def problem_spec
-- function signature
(impl: Int → Int × Int)
-- inputs
(num: Int) :=
-- spec
let spec (result: Int × Int) :=
  let (even_count, odd_count) := result;
  let numAbs := |num|.toNat;
  let numBy10 := numAbs/10;
  let (even_count', odd_count') := impl numBy10;
  (result = impl numAbs) ∧
  (0 ≤ num → (Even num ↔ 1 + even_count' = even_count) ∧ (Odd num ↔ even_count' = even_count)) ∧
  (0 ≤ num → (Odd num ↔ 1 + odd_count' = odd_count) ∧ (Even num ↔ odd_count' = odd_count));
-- program terminates
∃ result, impl num = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def count_even_odd_digits (n: Nat) : Nat × Nat :=
  if n = 0 then (1, 0)
  else
    let rec aux (n: Nat) : Nat × Nat :=
      if n = 0 then (0, 0)
      else
        let digit := n % 10
        let rest := n / 10
        let (even_rest, odd_rest) := aux rest
        if digit % 2 = 0 then
          (even_rest + 1, odd_rest)
        else
          (even_rest, odd_rest + 1)
    aux n

def implementation (num: Int) : Int × Int := 
  let n := |num|.toNat
  let (even_count, odd_count) := count_even_odd_digits n
  (Int.ofNat even_count, Int.ofNat odd_count)

-- LLM HELPER
lemma count_even_odd_digits_zero : count_even_odd_digits 0 = (1, 0) := by
  rfl

-- LLM HELPER
lemma count_even_odd_digits_nonzero (n: Nat) (h: n > 0) : 
  count_even_odd_digits n = 
  let digit := n % 10
  let rest := n / 10
  let (even_rest, odd_rest) := count_even_odd_digits rest
  if digit % 2 = 0 then
    (even_rest + 1, odd_rest)
  else
    (even_rest, odd_rest + 1) := by
  sorry

-- LLM HELPER
lemma implementation_recursive (num: Int) (h: 0 ≤ num) :
  let numAbs := |num|.toNat
  let numBy10 := numAbs / 10
  let (even_count, odd_count) := implementation num
  let (even_count', odd_count') := implementation numBy10
  (numAbs = 0 → even_count = 1 ∧ odd_count = 0) ∧
  (numAbs > 0 → 
    let digit := numAbs % 10
    if digit % 2 = 0 then
      even_count = even_count' + 1 ∧ odd_count = odd_count'
    else
      even_count = even_count' ∧ odd_count = odd_count' + 1) := by
  sorry

theorem correctness
(num: Int)
: problem_spec implementation num := by
  unfold problem_spec
  use implementation num
  constructor
  · rfl
  · unfold implementation
    simp only [abs_of_nonneg]
    sorry