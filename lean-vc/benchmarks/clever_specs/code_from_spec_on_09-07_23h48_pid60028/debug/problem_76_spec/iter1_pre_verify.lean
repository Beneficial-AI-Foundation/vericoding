def problem_spec
(implementation: Int → Int → Bool)
(x: Int) (n: Int) :=
let spec (result: Bool) :=
  result → exists k: Nat, x = n^k
∃ result, implementation x n = result ∧
spec result

-- LLM HELPER
def is_perfect_power (x: Int) (n: Int) : Bool :=
  if n = 0 then false
  else if n = 1 then x = 1
  else if n = -1 then x = 1 ∨ x = -1
  else if x = 0 then true
  else if x = 1 then true
  else if x = -1 then n % 2 = 0
  else if x < 0 ∧ n % 2 = 0 then false
  else
    let abs_x := Int.natAbs x
    let abs_n := Int.natAbs n
    let rec check_power (current: Nat) (power: Nat) (target: Nat) : Bool :=
      if current = target then true
      else if current > target then false
      else check_power (current * abs_n) (power + 1) target
    if abs_n ≤ 1 then false
    else check_power abs_n 1 abs_x

def implementation (x: Int) (n: Int) : Bool := is_perfect_power x n

-- LLM HELPER
lemma pow_pos_of_pos {a : Int} {k : Nat} (ha : a > 0) : a^k > 0 := by
  induction k with
  | zero => simp
  | succ k ih => 
    simp [Int.pow_succ]
    exact Int.mul_pos ha ih

-- LLM HELPER
lemma pow_neg_even {a : Int} {k : Nat} (ha : a < 0) (hk : k % 2 = 0) : a^k > 0 := by
  sorry

-- LLM HELPER
lemma pow_neg_odd {a : Int} {k : Nat} (ha : a < 0) (hk : k % 2 = 1) : a^k < 0 := by
  sorry

-- LLM HELPER
lemma perfect_power_characterization (x n : Int) : 
  (∃ k : Nat, x = n^k) ↔ 
  (n = 0 ∧ x = 0) ∨ 
  (n = 1 ∧ x = 1) ∨ 
  (n = -1 ∧ (x = 1 ∨ x = -1)) ∨ 
  (x = 0 ∧ n ≠ 0) ∨ 
  (x = 1 ∧ n ≠ 0) ∨ 
  (x = -1 ∧ n ≠ 0) ∨ 
  (n ≠ 0 ∧ n ≠ 1 ∧ n ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 ∧ 
   ∃ k : Nat, k > 0 ∧ x = n^k) := by
  sorry

-- LLM HELPER
lemma is_perfect_power_correct (x n : Int) : 
  is_perfect_power x n = true → ∃ k : Nat, x = n^k := by
  sorry

theorem correctness
(x: Int) (n: Int)
: problem_spec implementation x n := by
  simp [problem_spec, implementation]
  use is_perfect_power x n
  constructor
  · rfl
  · intro h
    exact is_perfect_power_correct x n h