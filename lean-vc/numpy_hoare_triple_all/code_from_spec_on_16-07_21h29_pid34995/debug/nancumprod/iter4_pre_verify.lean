import Std.Do.Triple
import Std.Tactic.Do

def nancumprod_helper {n : Nat} (arr : Vector Float n) (i : Nat) (acc : Float) : Float :=
  if h : i < n then
    let val := arr.get ⟨i, h⟩
    let new_acc := if Float.isNaN val then acc else acc * val
    nancumprod_helper arr (i + 1) new_acc
  else acc

-- LLM HELPER
lemma list_range_bound (i : Nat) (idx : Nat) (h : idx ∈ List.range (i + 1)) : idx ≤ i :=
  List.mem_range.mp h

-- LLM HELPER
lemma fin_bound_helper {n : Nat} (i : Fin n) (idx : Nat) (h : idx ∈ List.range (i.val + 1)) : idx < n := by
  have h1 : idx < i.val + 1 := List.mem_range.mp h
  have h2 : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
  exact Nat.lt_of_lt_of_le h1 h2

-- LLM HELPER
lemma range_mem_lt (i : Nat) (idx : Nat) : idx ∈ List.range (i + 1) → idx < i + 1 :=
  List.mem_range.mp

/-- Return the cumulative product of array elements treating NaNs as 1.
    The cumulative product does not change when NaNs are encountered and leading NaNs are replaced by ones. -/
def nancumprod {n : Nat} (arr : Vector Float n) : Id (Vector Float n) :=
  pure (Vector.ofFn (fun i => 
    (List.range (i.val + 1)).foldl (fun acc idx => 
      let val := arr.get ⟨idx, by 
        have h1 : idx ∈ List.range (i.val + 1) := by assumption
        have h2 : idx < i.val + 1 := range_mem_lt i.val idx h1
        have h3 : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
        exact Nat.lt_of_lt_of_le h2 h3⟩
      if Float.isNaN val then acc else acc * val) 1.0))

-- LLM HELPER
lemma triple_intro {α : Type*} {P : Prop} {Q : α → Prop} {m : Id α} :
  P → (∀ x, m = pure x → P → Q x) → (⦃⌜P⌝⦄ m ⦃⇓result => ⌜Q result⌝⦄) := by
  intro hp hq
  simp [Triple.lift]
  intro h_pre
  cases' m with val
  simp [pure] at hq
  exact hq val rfl hp

/-- Specification: nancumprod returns the cumulative product while treating NaN values as 1.
    This means:
    1. The resulting array has the same size as the input
    2. Each element is the product of all non-NaN elements from the start up to that position
    3. NaN values are treated as 1 in the product calculation
    4. Leading NaNs are replaced by ones
    5. The cumulative product property holds for non-NaN values -/
theorem nancumprod_spec {n : Nat} (arr : Vector Float n) :
    ⦃⌜True⌝⦄
    nancumprod arr
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- If all elements from start to i are NaN, result[i] = 1
      (∀ j : Fin n, j.val ≤ i.val → Float.isNaN (arr.get j)) → result.get i = 1.0 ∧
      -- If no elements from start to i are NaN, result[i] = product of all elements from start to i
      (∀ j : Fin n, j.val ≤ i.val → ¬Float.isNaN (arr.get j)) → 
        result.get i = (List.range (i.val + 1)).foldl (fun acc idx => acc * arr.get ⟨idx, by 
          have h1 : idx ∈ List.range (i.val + 1) := by assumption
          have h2 : idx < i.val + 1 := range_mem_lt i.val idx h1
          have h3 : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
          exact Nat.lt_of_lt_of_le h2 h3⟩) 1.0 ∧
      -- General case: result[i] = product of all non-NaN elements from start to i
      result.get i = (List.range (i.val + 1)).foldl (fun acc idx => 
        let val := arr.get ⟨idx, by 
          have h1 : idx ∈ List.range (i.val + 1) := by assumption
          have h2 : idx < i.val + 1 := range_mem_lt i.val idx h1
          have h3 : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
          exact Nat.lt_of_lt_of_le h2 h3⟩
        if Float.isNaN val then acc else acc * val) 1.0⌝⦄ := by
  apply triple_intro
  · simp
  · intro result h_result
    simp [nancumprod] at h_result
    rw [← h_result]
    intro i
    constructor
    · intro h_all_nan
      simp [Vector.get, Vector.ofFn]
      rfl
    constructor
    · intro h_no_nan
      simp [Vector.get, Vector.ofFn]
      rfl
    · simp [Vector.get, Vector.ofFn]
      rfl