def problem_spec
-- function signature
(implementation: Int → List Int)
-- inputs
(n: Int) :=
-- spec
let spec (result: List Int) :=
  result.length = n ∧
  (forall i: Nat, (1 <= i ∧ i < n) → (result[i]! = result[i-1]! + 2)) ∧
  result[0]! = n
-- program termination
∃ result, implementation n = result ∧
spec result

def implementation (n: Int) : List Int := 
  if n <= 0 then [] else List.map (fun i => n + 2 * ↑i) (List.range n.natAbs)

-- LLM HELPER
lemma list_range_map_length (n: Nat) (f: Nat → Int) : 
  (List.map f (List.range n)).length = n := by
  simp [List.length_map, List.length_range]

-- LLM HELPER
lemma list_range_map_get (n: Nat) (f: Nat → Int) (i: Nat) (h: i < n) :
  (List.map f (List.range n))[i]! = f i := by
  simp [List.get!_eq_get, List.get_map, List.get_range]

-- LLM HELPER
lemma int_natabs_pos (n: Int) (h: n > 0) : n.natAbs > 0 := by
  simp [Int.natAbs_pos]
  exact h

-- LLM HELPER
lemma int_cast_natabs (n: Int) (h: n > 0) : ↑n.natAbs = n := by
  simp [Int.natAbs_of_nonneg (le_of_lt h)]

theorem correctness
(n: Int)
: problem_spec implementation n := by
  unfold problem_spec implementation
  if h : n <= 0 then
    simp [h]
    use []
    constructor
    · rfl
    · simp
      constructor
      · simp [List.length_nil]
        exact h
      · constructor
        · intro i hi
          simp at hi
          omega
        · simp
  else
    simp [h]
    use List.map (fun i => n + 2 * ↑i) (List.range n.natAbs)
    constructor
    · rfl
    · simp
      constructor
      · rw [list_range_map_length]
        have n_pos : n > 0 := by omega
        rw [int_cast_natabs n n_pos]
      · constructor
        · intro i hi
          have n_pos : n > 0 := by omega
          have i_bound : i < n.natAbs := by
            rw [int_cast_natabs n n_pos] at hi
            exact hi.2
          have i_pred_bound : i - 1 < n.natAbs := by omega
          rw [list_range_map_get n.natAbs (fun i => n + 2 * ↑i) i i_bound]
          rw [list_range_map_get n.natAbs (fun i => n + 2 * ↑i) (i-1) i_pred_bound]
          simp
          ring
        · have n_pos : n > 0 := by omega
          have zero_bound : 0 < n.natAbs := by
            rw [int_cast_natabs n n_pos]
            exact n_pos
          rw [list_range_map_get n.natAbs (fun i => n + 2 * ↑i) 0 zero_bound]
          simp