def problem_spec
-- function signature
(impl: List Int → Option Int)
-- inputs
(arr: List Int) :=
-- spec
let spec (result: Option Int) :=
  match result with
  | none => arr = []
  | some result =>
    let magnitude_sum := (arr.map (fun x => Int.ofNat x.natAbs)).sum
    let neg_count_odd := (arr.filter (fun x => x < 0)).length % 2 = 1
    let has_zero := 0 ∈ arr
    (result < 0 ↔ (neg_count_odd ∧ ¬has_zero)) ∧
    (result > 0 ↔ (¬neg_count_odd ∧ ¬has_zero)) ∧
    (result = 0 ↔ has_zero) ∧
    (result < 0 → result = magnitude_sum * -1) ∧
    (result > 0 → result = magnitude_sum)
-- program terminates
∃ result, impl arr = result ∧
-- return value satisfies spec
spec result

def implementation (arr: List Int) : Option Int := 
  if arr = [] then 
    none
  else if 0 ∈ arr then 
    some 0
  else
    let magnitude_sum := (arr.map (fun x => Int.ofNat x.natAbs)).sum
    let neg_count_odd := (arr.filter (fun x => x < 0)).length % 2 = 1
    if neg_count_odd then
      some (magnitude_sum * -1)
    else
      some magnitude_sum

-- LLM HELPER
lemma magnitude_sum_nonneg (arr: List Int) :
  (arr.map (fun x => Int.ofNat x.natAbs)).sum ≥ 0 := by
  exact Int.coe_nat_nonneg _

-- LLM HELPER
lemma magnitude_sum_pos_of_nonempty_no_zero (arr: List Int) :
  arr ≠ [] → 0 ∉ arr → (arr.map (fun x => Int.ofNat x.natAbs)).sum > 0 := by
  intro h1 h2
  have : arr.length > 0 := by
    rw [List.length_pos_iff_ne_nil]
    exact h1
  have : ∃ x, x ∈ arr := by
    cases arr with
    | nil => contradiction
    | cons head tail => use head; simp
  obtain ⟨x, hx⟩ := this
  have : x ≠ 0 := fun h => h2 (h ▸ hx)
  have : x.natAbs > 0 := Int.natAbs_pos.mpr this
  have : (Int.ofNat x.natAbs) > 0 := Int.coe_nat_pos.mpr this
  exact List.sum_pos_of_mem_of_pos (List.mem_map_of_mem _ hx) this

-- LLM HELPER
lemma empty_case (arr: List Int) :
  arr = [] → implementation arr = none := by
  intro h
  simp [implementation, h]

-- LLM HELPER
lemma zero_case (arr: List Int) :
  arr ≠ [] → 0 ∈ arr → implementation arr = some 0 := by
  intro h1 h2
  simp [implementation, h1, h2]

-- LLM HELPER
lemma neg_odd_case (arr: List Int) :
  arr ≠ [] → 0 ∉ arr → (arr.filter (fun x => x < 0)).length % 2 = 1 →
  implementation arr = some ((arr.map (fun x => Int.ofNat x.natAbs)).sum * -1) := by
  intro h1 h2 h3
  simp [implementation, h1, h2, h3]

-- LLM HELPER
lemma neg_even_case (arr: List Int) :
  arr ≠ [] → 0 ∉ arr → (arr.filter (fun x => x < 0)).length % 2 ≠ 1 →
  implementation arr = some (arr.map (fun x => Int.ofNat x.natAbs)).sum := by
  intro h1 h2 h3
  simp [implementation, h1, h2, h3]

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  use implementation arr
  constructor
  · rfl
  · simp [problem_spec]
    by_cases h1 : arr = []
    · simp [empty_case arr h1, h1]
    · by_cases h2 : 0 ∈ arr
      · simp [zero_case arr h1 h2, h2]
      · by_cases h3 : (arr.filter (fun x => x < 0)).length % 2 = 1
        · simp [neg_odd_case arr h1 h2 h3]
          let magnitude_sum := (arr.map (fun x => Int.ofNat x.natAbs)).sum
          constructor
          · constructor
            · intro h
              constructor
              · exact h3
              · exact h2
            · intro ⟨h4, h5⟩
              simp [Int.mul_neg_one]
              exact Int.neg_pos.mpr (magnitude_sum_pos_of_nonempty_no_zero arr h1 h2)
          · constructor
            · constructor
              · intro h
                exfalso
                have : magnitude_sum * -1 < 0 := by
                  simp [Int.mul_neg_one]
                  exact Int.neg_pos.mpr (magnitude_sum_pos_of_nonempty_no_zero arr h1 h2)
                exact Int.lt_irrefl _ (Int.lt_trans this h)
              · intro ⟨h4, h5⟩
                exfalso
                exact h3 h4
            · constructor
              · intro h
                exfalso
                have : magnitude_sum * -1 ≠ 0 := by
                  simp [Int.mul_neg_one]
                  exact Int.neg_ne_zero.mpr (Int.ne_of_gt (magnitude_sum_pos_of_nonempty_no_zero arr h1 h2))
                exact this h.symm
              · intro h
                exact h2
            · constructor
              · intro h
                rfl
              · intro h
                exfalso
                have : magnitude_sum * -1 ≠ 0 := by
                  simp [Int.mul_neg_one]
                  exact Int.neg_ne_zero.mpr (Int.ne_of_gt (magnitude_sum_pos_of_nonempty_no_zero arr h1 h2))
                exact this h
        · simp [neg_even_case arr h1 h2 h3]
          let magnitude_sum := (arr.map (fun x => Int.ofNat x.natAbs)).sum
          constructor
          · constructor
            · intro h
              exfalso
              have : magnitude_sum ≥ 0 := magnitude_sum_nonneg arr
              exact Int.not_lt.mpr this h
            · intro ⟨h4, h5⟩
              exfalso
              exact h3 h4
          · constructor
            · constructor
              · intro h
                constructor
                · exact h3
                · exact h2
              · intro ⟨h4, h5⟩
                exact magnitude_sum_pos_of_nonempty_no_zero arr h1 h2
            · constructor
              · intro h
                exfalso
                have : magnitude_sum > 0 := magnitude_sum_pos_of_nonempty_no_zero arr h1 h2
                exact Int.lt_irrefl _ (Int.lt_trans h this)
              · intro h
                exact h2
            · constructor
              · intro h
                rfl
              · intro h
                exfalso
                have : magnitude_sum > 0 := magnitude_sum_pos_of_nonempty_no_zero arr h1 h2
                exact Int.lt_irrefl _ (h ▸ this)