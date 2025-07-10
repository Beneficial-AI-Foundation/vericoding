def problem_spec
-- function signature
(implementation: Int → List Int)
-- inputs
(n: Int) :=
-- spec
let spec (result: List Int) :=
  (result.length = n) ∧
  (forall i: Nat, (1 ≤ i ∧ i ≤ n ∧ Even i) → (result[i-1]! = Nat.factorial i)) ∧
  (forall i: Nat, (1 ≤ i ∧ i ≤ n ∧ Odd i) → (result[i-1]! = (List.range (i+1)).sum))
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def compute_element (i: Nat) : Int :=
  if Even i then 
    Int.ofNat (Nat.factorial i)
  else 
    Int.ofNat ((List.range (i+1)).sum)

def implementation (n: Int) : List Int := 
  if n ≤ 0 then 
    []
  else 
    (List.range n.natAbs).map (fun i => compute_element (i + 1))

-- LLM HELPER
lemma range_sum_formula (k: Nat) : (List.range (k+1)).sum = k * (k + 1) / 2 := by
  induction k with
  | zero => simp [List.range, List.sum]
  | succ k ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons]
    rw [List.sum_range, ih]
    simp [Nat.succ_mul, Nat.add_mul, Nat.mul_succ]
    ring

-- LLM HELPER
lemma list_length_map_range (n: Nat) (f: Nat → Int) : 
  ((List.range n).map f).length = n := by
  rw [List.length_map, List.length_range]

-- LLM HELPER
lemma getElem_map_range (n: Nat) (f: Nat → Int) (i: Nat) (h: i < n) :
  ((List.range n).map f)[i]! = f i := by
  rw [List.getElem_map, List.getElem_range]

-- LLM HELPER
lemma natAbs_pos_of_pos (n: Int) (h: 0 < n) : 0 < n.natAbs := by
  rw [Int.natAbs_pos]
  exact Ne.symm (ne_of_gt h)

theorem correctness
(n: Int)
: problem_spec implementation n := by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · simp [implementation]
    split_ifs with h
    · simp
      constructor
      · simp
      · constructor <;> intro i hi; simp at hi
    · constructor
      · simp [list_length_map_range]
        exact Int.natAbs_of_nonneg (le_of_not_gt h)
      · constructor
        · intro i hi
          simp at hi
          have h_pos : 0 < n := by
            by_contra h_neg
            simp at h_neg
            exact h h_neg
          have h_bound : i - 1 < n.natAbs := by
            rw [Int.natAbs_of_nonneg (le_of_lt h_pos)]
            exact Nat.sub_lt_of_pos_le (Nat.pos_of_ne_zero (ne_of_gt hi.1)) hi.2
          rw [getElem_map_range _ _ (i-1) h_bound]
          simp [compute_element]
          rw [if_pos hi.3]
          rfl
        · intro i hi
          simp at hi
          have h_pos : 0 < n := by
            by_contra h_neg
            simp at h_neg
            exact h h_neg
          have h_bound : i - 1 < n.natAbs := by
            rw [Int.natAbs_of_nonneg (le_of_lt h_pos)]
            exact Nat.sub_lt_of_pos_le (Nat.pos_of_ne_zero (ne_of_gt hi.1)) hi.2
          rw [getElem_map_range _ _ (i-1) h_bound]
          simp [compute_element]
          rw [if_neg]
          · rfl
          · exact Nat.odd_iff_not_even.mp hi.3