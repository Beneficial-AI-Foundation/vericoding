def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: List Int) :=
  l.length = result.length ∧
  let every_third_idx := (List.range l.length).filter (λ i => i % 3 = 0);
  let every_third_val_in_result := every_third_idx.map (λ i => result[i]!);
  let every_third_val := every_third_idx.map (λ i => l[i]!);
  (∀ i, i < l.length → (i % 3 ≠ 0 → l[i]! = result[i]!)) ∧
  List.Sorted (· ≤ ·) every_third_val_in_result ∧
  every_third_val.all (λ x => every_third_val_in_result.count x = every_third_val.count x);
-- program termination
∃ result, implementation l = result ∧
spec result

def implementation (l: List Int) : List Int := 
  let indices := List.range l.length |>.filter (λ i => i % 3 = 0)
  let values := indices.map (λ i => l[i]!)
  let sorted_values := values.toArray.qsort (· ≤ ·) |>.toList
  
  let rec build_result (i: Nat) (sorted_vals: List Int) : List Int :=
    if i >= l.length then []
    else if i % 3 = 0 then
      match sorted_vals with
      | [] => (l[i]!) :: build_result (i + 1) []
      | v :: vs => v :: build_result (i + 1) vs
    else
      (l[i]!) :: build_result (i + 1) sorted_vals
  
  build_result 0 sorted_values

-- LLM HELPER
lemma build_result_length (l: List Int) (i: Nat) (sorted_vals: List Int) :
  (build_result l i sorted_vals).length = if i >= l.length then 0 else l.length - i := by
  induction' h : l.length - i using Nat.strong_induction_on with n ih
  simp [build_result]
  if h_ge : i >= l.length then
    simp [h_ge]
  else
    simp [h_ge]
    if h_mod : i % 3 = 0 then
      simp [h_mod]
      cases sorted_vals with
      | nil => 
        simp
        rw [ih]
        simp
        omega
        omega
      | cons v vs => 
        simp
        rw [ih]
        simp
        omega
        omega
    else
      simp [h_mod]
      rw [ih]
      simp
      omega
      omega

-- LLM HELPER
lemma implementation_length (l: List Int) : (implementation l).length = l.length := by
  unfold implementation
  rw [build_result_length]
  simp

-- LLM HELPER
lemma build_result_preserves_non_third (l: List Int) (i: Nat) (sorted_vals: List Int) :
  ∀ j, i ≤ j → j < l.length → j % 3 ≠ 0 → (build_result l i sorted_vals)[j - i]! = l[j]! := by
  intro j h_ge h_lt h_not_mod
  generalize h_n : l.length - i = n
  induction' n using Nat.strong_induction_on with n ih generalizing i
  unfold build_result
  if h_ge_len : i >= l.length then
    omega
  else
    simp [h_ge_len]
    if h_mod_i : i % 3 = 0 then
      simp [h_mod_i]
      cases sorted_vals with
      | nil => 
        if h_eq : i = j then
          rw [h_eq] at h_not_mod
          contradiction
        else
          have : i + 1 ≤ j := by omega
          rw [← Nat.sub_add_cancel this]
          simp
          apply ih
          omega
          omega
          omega
          exact h_lt
          exact h_not_mod
      | cons v vs => 
        if h_eq : i = j then
          rw [h_eq] at h_not_mod
          contradiction
        else
          have : i + 1 ≤ j := by omega
          rw [← Nat.sub_add_cancel this]
          simp
          apply ih
          omega
          omega
          omega
          exact h_lt
          exact h_not_mod
    else
      simp [h_mod_i]
      if h_eq : i = j then
        rw [h_eq]
        simp
      else
        have : i + 1 ≤ j := by omega
        rw [← Nat.sub_add_cancel this]
        simp
        apply ih
        omega
        omega
        omega
        exact h_lt
        exact h_not_mod

-- LLM HELPER
lemma implementation_preserves_non_third (l: List Int) (i: Nat) :
  i < l.length → i % 3 ≠ 0 → (implementation l)[i]! = l[i]! := by
  intros h_lt h_not_third
  unfold implementation
  convert build_result_preserves_non_third l 0 _ i _ h_lt h_not_third
  simp

theorem correctness
(l: List Int)
: problem_spec implementation l := by
  use implementation l
  constructor
  · rfl
  · constructor
    · exact implementation_length l
    · constructor
      · intros i hi h_not_third
        exact implementation_preserves_non_third l i hi h_not_third
      · constructor
        · simp [List.Sorted]
        · simp [List.all_iff_forall]
          intro x h_mem
          rfl