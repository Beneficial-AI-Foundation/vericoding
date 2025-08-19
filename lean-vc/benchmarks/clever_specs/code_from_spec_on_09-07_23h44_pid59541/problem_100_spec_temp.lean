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

-- LLM HELPER
def implementation (n: Int) : List Int := 
  if n <= 0 then [] else List.range n.natAbs |>.map (fun i => n + 2 * i)

-- LLM HELPER
lemma list_range_map_length (n: Nat) (f: Nat → Int) : 
  (List.range n |>.map f).length = n := by
  simp [List.length_map, List.length_range]

-- LLM HELPER  
lemma list_range_map_get (n: Nat) (f: Nat → Int) (i: Nat) (h: i < n) :
  (List.range n |>.map f)[i]! = f i := by
  rw [List.getElem!_pos]
  · simp [List.getElem_map, List.getElem_range h]
  · simp [List.length_map, List.length_range]
    exact h

-- LLM HELPER
lemma natAbs_pos_of_pos (n: Int) (h: 0 < n) : 0 < n.natAbs := by
  rw [Int.natAbs_of_nonneg (le_of_lt h)]
  exact Int.natCast_pos.mp h

theorem correctness
(n: Int)
: problem_spec implementation n := by
  unfold problem_spec implementation
  if h : n <= 0 then
    use []
    constructor
    · simp [h]
    · simp
      constructor
      · simp
      · constructor
        · intros i hi
          simp at hi
          omega
        · simp
  else
    have n_pos : 0 < n := by omega
    use List.range n.natAbs |>.map (fun i => n + 2 * i)
    constructor
    · simp [h]
    · constructor
      · rw [list_range_map_length]
        rw [Int.natAbs_of_nonneg (le_of_lt n_pos)]
        exact Int.natCast_inj.mp rfl
      · constructor
        · intros i hi
          have i_bound : i < n.natAbs := by
            rw [Int.natAbs_of_nonneg (le_of_lt n_pos)] at hi ⊢
            exact Int.natCast_lt.mp hi.2
          have i_prev_bound : i - 1 < n.natAbs := by omega
          rw [list_range_map_get n.natAbs (fun j => n + 2 * j) i i_bound]
          rw [list_range_map_get n.natAbs (fun j => n + 2 * j) (i-1) i_prev_bound]
          simp
          ring
        · have zero_lt_natAbs : 0 < n.natAbs := natAbs_pos_of_pos n n_pos
          rw [list_range_map_get n.natAbs (fun j => n + 2 * j) 0 zero_lt_natAbs]
          simp