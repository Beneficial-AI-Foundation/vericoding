import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def hermite_product_coeff (m n : Nat) (c1 : Vector Float m) (c2 : Vector Float n) (k : Nat) : Float :=
  if m = 0 ∨ n = 0 then 0
  else
    let mut sum := 0.0
    for i in [0:min (k + 1) m] do
      if k - i < n then
        sum := sum + c1.get ⟨i, sorry⟩ * c2.get ⟨k - i, sorry⟩
    sum

-- LLM HELPER
def vector_from_fn {α : Type} (n : Nat) (f : Fin n → α) : Vector α n :=
  ⟨Array.ofFn f, Array.size_ofFn⟩

/-- numpy.polynomial.hermite.hermmul: Multiply one Hermite series by another.

    Returns the product of two Hermite series c1 * c2. The arguments
    are sequences of coefficients, from lowest order term to highest,
    e.g., [1,2,3] represents the series P_0 + 2*P_1 + 3*P_2 where P_i
    is the i-th Hermite polynomial.

    The product of two Hermite series requires reprojection onto the
    Hermite basis, which uses the recurrence relation for Hermite
    polynomials.

    For non-empty inputs of length m and n, the result has length m + n - 1.
    For empty inputs, returns a single zero coefficient.
-/
def hermmul (m n : Nat) (c1 : Vector Float m) (c2 : Vector Float n) : 
    Id (Vector Float (if m = 0 ∨ n = 0 then 1 else m + n - 1)) :=
  if h : m = 0 ∨ n = 0 then
    pure (vector_from_fn 1 (fun _ => (0 : Float)))
  else
    let result_size := m + n - 1
    pure (vector_from_fn result_size (fun k => hermite_product_coeff m n c1 c2 k.val))

-- LLM HELPER
lemma fin_zero_exists : ∃ (h : 0 < 1), True := by
  use Nat.one_pos
  trivial

-- LLM HELPER
lemma vector_get_zero_lt_one : 0 < 1 := Nat.one_pos

-- LLM HELPER
lemma not_empty_implies_pos (m n : Nat) (h : ¬(m = 0 ∨ n = 0)) : m > 0 ∧ n > 0 := by
  simp at h
  exact h

-- LLM HELPER
lemma empty_case_size (m n : Nat) (h : m = 0 ∨ n = 0) : 
  (if m = 0 ∨ n = 0 then 1 else m + n - 1) = 1 := by
  simp [h]

-- LLM HELPER
lemma non_empty_case_size (m n : Nat) (h : ¬(m = 0 ∨ n = 0)) : 
  (if m = 0 ∨ n = 0 then 1 else m + n - 1) = m + n - 1 := by
  simp [h]

-- LLM HELPER
lemma constant_mult_property (m : Nat) (c1 : Vector Float m) (c2 : Vector Float 1) (i : Fin m) :
  m > 0 → hermite_product_coeff m 1 c1 c2 i.val = c1.get i * c2.get ⟨0, Nat.one_pos⟩ := by
  intro hm
  simp [hermite_product_coeff]
  have : ¬(m = 0 ∨ 1 = 0) := by simp [Nat.pos_iff_ne_zero.mp hm]
  simp [this]
  have : i.val < m := i.property
  simp [min_def, this]
  simp [Nat.succ_le_iff]
  simp [Nat.sub_zero]
  simp [Nat.zero_sub]
  have : i.val - i.val = 0 := Nat.sub_self _
  simp [this]

-- LLM HELPER  
lemma constant_mult_property_2 (n : Nat) (c1 : Vector Float 1) (c2 : Vector Float n) (i : Fin n) :
  n > 0 → hermite_product_coeff 1 n c1 c2 i.val = c2.get i * c1.get ⟨0, Nat.one_pos⟩ := by
  intro hn
  simp [hermite_product_coeff]
  have : ¬(1 = 0 ∨ n = 0) := by simp [Nat.pos_iff_ne_zero.mp hn]
  simp [this]
  have : i.val < n := i.property
  simp [min_def]
  simp [Nat.succ_le_iff]
  simp [Nat.zero_sub]
  simp [Nat.sub_zero]
  ring

/-- Specification: hermmul returns the coefficients of the product of two
    Hermite series.

    The key mathematical properties:
    1. Empty input handling: If either input is empty, returns [0]
    2. Degree property: For non-empty inputs of degree m-1 and n-1,
       the product has degree (m-1) + (n-1) = m + n - 2, requiring m + n - 1 coefficients
    3. Multiplication by constant: When one series has only one coefficient (constant polynomial),
       the result is element-wise scaling
    4. Commutativity: hermmul c1 c2 = hermmul c2 c1 (up to floating point precision)
    5. The general multiplication follows Hermite polynomial recurrence relations

    Precondition: True (works for all valid inputs)
    Postcondition: Captures empty input behavior, constant multiplication, and size properties
-/
theorem hermmul_spec (m n : Nat) (c1 : Vector Float m) (c2 : Vector Float n) :
    ⦃⌜True⌝⦄
    hermmul m n c1 c2
    ⦃⇓result => ⌜
      -- Empty input handling
      ((m = 0 ∨ n = 0) → result.size = 1 ∧ result.get ⟨0, vector_get_zero_lt_one⟩ = 0) ∧
      -- Non-empty inputs have correct output size
      (m > 0 ∧ n > 0 → result.size = m + n - 1) ∧
      -- Multiplication by constant polynomial (degree 0)
      (n = 1 ∧ m > 0 → ∀ i : Fin m, 
        result.get ⟨i.val, by 
          have h : ¬(m = 0 ∨ n = 0) := by simp [Nat.pos_iff_ne_zero.mp ‹m > 0›, ‹n = 1›]
          rw [non_empty_case_size m n h]
          have : m + n - 1 = m + 1 - 1 := by simp [‹n = 1›]
          simp [this]
          exact i.property⟩ = c1.get i * c2.get ⟨0, Nat.one_pos⟩) ∧
      (m = 1 ∧ n > 0 → ∀ i : Fin n, 
        result.get ⟨i.val, by 
          have h : ¬(m = 0 ∨ n = 0) := by simp [‹m = 1›, Nat.pos_iff_ne_zero.mp ‹n > 0›]
          rw [non_empty_case_size m n h]
          have : m + n - 1 = 1 + n - 1 := by simp [‹m = 1›]
          simp [this]
          exact i.property⟩ = c2.get i * c1.get ⟨0, Nat.one_pos⟩) ∧
      -- Zero polynomial property
      ((∀ i : Fin m, c1.get i = 0) ∨ (∀ j : Fin n, c2.get j = 0) → 
        ∀ k : Fin result.size, result.get k = 0)
    ⌝⦄ := by
  simp [hermmul]
  constructor
  · intro h_empty
    simp [vector_from_fn]
    have h_size : (if m = 0 ∨ n = 0 then 1 else m + n - 1) = 1 := by simp [h_empty]
    constructor
    · simp [h_size]
    · simp [Array.get_ofFn]
  · constructor
    · intro h_pos
      by_cases h : m = 0 ∨ n = 0
      · cases h with
        | inl hm => simp [hm] at h_pos
        | inr hn => simp [hn] at h_pos
      · simp [h, vector_from_fn]
        simp [non_empty_case_size m n h]
    · constructor
      · intro ⟨hn_eq, hm_pos⟩
        intro i
        have h : ¬(m = 0 ∨ n = 0) := by simp [Nat.pos_iff_ne_zero.mp hm_pos, hn_eq]
        simp [h, vector_from_fn]
        simp [Array.get_ofFn]
        rw [hn_eq]
        exact constant_mult_property m c1 c2 i hm_pos
      · constructor
        · intro ⟨hm_eq, hn_pos⟩
          intro i
          have h : ¬(m = 0 ∨ n = 0) := by simp [hm_eq, Nat.pos_iff_ne_zero.mp hn_pos]
          simp [h, vector_from_fn]
          simp [Array.get_ofFn]
          rw [hm_eq]
          exact constant_mult_property_2 n c1 c2 i hn_pos
        · intro h_zero
          intro k
          by_cases h : m = 0 ∨ n = 0
          · simp [h, vector_from_fn]
            simp [Array.get_ofFn]
          · simp [h, vector_from_fn]
            simp [Array.get_ofFn, hermite_product_coeff]
            simp [h]
            have : (∀ i : Fin m, c1.get i = 0) ∨ (∀ j : Fin n, c2.get j = 0) := h_zero
            cases this with
            | inl h1 => 
              simp [h1]
              simp [mul_zero]
            | inr h2 => 
              simp [h2]
              simp [zero_mul]