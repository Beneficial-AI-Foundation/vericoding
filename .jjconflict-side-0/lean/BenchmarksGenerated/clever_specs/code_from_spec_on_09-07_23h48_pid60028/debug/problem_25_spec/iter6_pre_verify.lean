def problem_spec
-- function signature
(implementation: Nat → List Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: List Nat) :=
2 ≤ n →
(result.foldl (· * ·) 1 = n ∧
List.Sorted (· ≤ ·) result ∧
result.all (fun i => n % i = 0 ∧ Nat.Prime i));
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def prime_factors_aux (n: Nat) (d: Nat) (acc: List Nat) : List Nat :=
  if n ≤ 1 then acc
  else if d * d > n then
    if n > 1 then n :: acc else acc
  else if n % d = 0 then
    prime_factors_aux (n / d) d (d :: acc)
  else
    prime_factors_aux n (d + 1) acc
termination_by n + d
decreasing_by
  simp_wf
  · have h1 : 0 < n := by
      have : n > 1 := by
        by_contra h
        simp at h
        have : n ≤ 1 := Nat.le_of_not_gt h
        contradiction
      linarith
    have h2 : 1 < d := by
      by_contra h
      simp at h
      have : d ≤ 1 := Nat.le_of_not_gt h
      interval_cases d
      · simp at *
      · have : 1 * 1 > n := by assumption
        simp at this
        have : n > 1 := by
          by_contra h
          simp at h
          have : n ≤ 1 := Nat.le_of_not_gt h
          contradiction
        linarith
    have : n / d < n := Nat.div_lt_self h1 h2
    linarith
  · simp_arith

def implementation (n: Nat) : List Nat := 
  (prime_factors_aux n 2 []).reverse

-- LLM HELPER
lemma prime_factors_aux_correct (n d: Nat) (acc: List Nat) :
  n ≥ 1 → d ≥ 2 → 
  let result := prime_factors_aux n d acc
  ∀ p ∈ result, Nat.Prime p ∧ n % p = 0 := by
  sorry

-- LLM HELPER
lemma prime_factors_aux_prod (n d: Nat) (acc: List Nat) :
  n ≥ 1 → d ≥ 2 → acc.foldl (· * ·) 1 = 1 →
  (prime_factors_aux n d acc).foldl (· * ·) 1 = n * acc.foldl (· * ·) 1 := by
  sorry

-- LLM HELPER
lemma prime_factors_aux_sorted (n d: Nat) (acc: List Nat) :
  n ≥ 1 → d ≥ 2 → List.Sorted (· ≤ ·) acc →
  List.Sorted (· ≤ ·) (prime_factors_aux n d acc) := by
  sorry

-- LLM HELPER
lemma list_reverse_prod (l: List Nat) :
  l.reverse.foldl (· * ·) 1 = l.foldl (· * ·) 1 := by
  induction l with
  | nil => simp
  | cons h t ih => 
    simp [List.reverse_cons, List.foldl_append]
    rw [ih]
    simp [List.foldl_cons]

-- LLM HELPER
lemma list_reverse_sorted (l: List Nat) :
  List.Sorted (· ≤ ·) l → List.Sorted (· ≤ ·) l.reverse := by
  sorry

-- LLM HELPER
lemma list_all_reverse (l: List Nat) (p: Nat → Bool) :
  l.reverse.all p = l.all p := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [List.reverse_cons, List.all_append]
    rw [ih]
    simp [List.all_cons]

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec, implementation]
  exists (prime_factors_aux n 2 []).reverse
  constructor
  · rfl
  · intro h
    constructor
    · rw [list_reverse_prod]
      have h1 : n ≥ 1 := by linarith
      have h2 : 2 ≥ 2 := by norm_num
      have h3 : ([] : List Nat).foldl (· * ·) 1 = 1 := by simp
      have := prime_factors_aux_prod n 2 [] h1 h2 h3
      simp at this
      exact this
    constructor
    · apply list_reverse_sorted
      apply prime_factors_aux_sorted
      · linarith
      · norm_num
      · constructor
    · rw [list_all_reverse]
      intro p hp
      constructor
      · have := prime_factors_aux_correct n 2 [] (by linarith) (by norm_num)
        exact (this p hp).2
      · have := prime_factors_aux_correct n 2 [] (by linarith) (by norm_num)
        exact (this p hp).1