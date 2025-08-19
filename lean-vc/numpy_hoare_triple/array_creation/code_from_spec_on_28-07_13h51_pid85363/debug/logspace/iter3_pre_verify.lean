import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

def problem_spec {num : Nat} (f : Float → Float → Bool → Float → Id (Vector Float num)) 
    (start stop : Float) (endpoint : Bool) (base : Float) : Prop :=
  ∀ (h_base_pos : base > 0) (h_base_ne_one : base ≠ 1) (h_num_pos : num > 0),
    ⦃⌜base > 0 ∧ base ≠ 1 ∧ num > 0⌝⦄
    f start stop endpoint base
    ⦃⇓result => ⌜
      -- Define the step size based on endpoint parameter
      let step := if endpoint ∧ num > 1 then (stop - start) / (num - 1).toFloat 
                  else (stop - start) / num.toFloat
      -- Each element follows the logarithmic spacing formula
      (∀ i : Fin num, result.get i = base ^ (start + i.val.toFloat * step)) ∧
      -- First element is always base^start
      (result.get ⟨0, h_num_pos⟩ = base ^ start) ∧
      -- Last element is base^stop when endpoint is true and num > 1
      (endpoint ∧ num > 1 → result.get ⟨num - 1, by omega⟩ = base ^ stop) ∧
      -- All elements are positive when base is positive
      (∀ i : Fin num, result.get i > 0)
    ⌝⦄

def logspace {num : Nat} (start stop : Float) (endpoint : Bool) (base : Float) : Id (Vector Float num) :=
  let step := if endpoint ∧ num > 1 then (stop - start) / (num - 1).toFloat 
              else (stop - start) / num.toFloat
  pure (Vector.ofFn (fun i => base ^ (start + i.val.toFloat * step)))

-- LLM HELPER
lemma vector_ofFn_get {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f).get i = f i := by
  simp [Vector.ofFn, Vector.get]

-- LLM HELPER
lemma pow_pos_of_base_pos (base : Float) (exp : Float) (h : base > 0) : base ^ exp > 0 := by
  sorry

-- LLM HELPER
lemma first_element_formula {num : Nat} (start stop : Float) (endpoint : Bool) (h_num_pos : num > 0) :
  let step := if endpoint ∧ num > 1 then (stop - start) / (num - 1).toFloat 
              else (stop - start) / num.toFloat
  start + (0 : Float) * step = start := by
  simp

-- LLM HELPER
lemma last_element_formula {num : Nat} (start stop : Float) (h_num_gt_one : num > 1) :
  let step := (stop - start) / (num - 1).toFloat
  start + (num - 1).toFloat * step = stop := by
  simp only [step]
  field_simp
  ring

theorem correctness {num : Nat} (start stop : Float) (endpoint : Bool) (base : Float) :
    problem_spec logspace start stop endpoint base := by
  intro h_base_pos h_base_ne_one h_num_pos
  simp [logspace]
  constructor
  · exact ⟨h_base_pos, h_base_ne_one, h_num_pos⟩
  · constructor
    · intro i
      rw [vector_ofFn_get]
    · constructor
      · rw [vector_ofFn_get]
        simp [first_element_formula]
      · constructor
        · intro h_endpoint h_num_gt_one
          rw [vector_ofFn_get]
          simp only [if_pos ⟨h_endpoint, h_num_gt_one⟩]
          rw [last_element_formula h_num_gt_one]
        · intro i
          rw [vector_ofFn_get]
          exact pow_pos_of_base_pos base _ h_base_pos