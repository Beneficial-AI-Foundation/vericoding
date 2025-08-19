import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def hermder_step {n : Nat} (c : Vector Float n) (scl : Float) : Vector Float (n - min 1 n) :=
  if h : n = 0 then
    Vector.mk []
  else
    have : n > 0 := Nat.pos_of_ne_zero h
    have : n - 1 < n := Nat.sub_lt this (by norm_num)
    Vector.mk (List.range (n - 1) |>.map (fun i => 
      scl * (2.0 * (i + 1 : Nat).toFloat) * c.get ⟨i + 1, by simp [Nat.add_lt_of_lt_sub]; exact Nat.lt_of_succ_le (Nat.succ_le_of_lt (List.mem_range.mp (by assumption)))⟩))

-- LLM HELPER
def hermder_aux {n : Nat} (c : Vector Float n) (m : Nat) (scl : Float) : Vector Float (n - min m n) :=
  if m = 0 then
    by simp [min_def]; exact c
  else if h : n = 0 then
    Vector.mk []
  else
    match m with
    | 0 => by simp [min_def]; exact c
    | Nat.succ m' =>
      if h' : n ≤ m then
        Vector.mk []
      else
        let step_result := hermder_step c scl
        have : n - 1 - min m' (n - 1) = n - min (m' + 1) n := by
          simp [Nat.succ_eq_add_one] at *
          sorry
        hermder_aux step_result m' scl

/-- Differentiate a Hermite series.
    Returns the Hermite series coefficients differentiated `m` times.
    At each iteration the result is multiplied by `scl` (scaling factor).
    The coefficients are from low to high degree. -/
def hermder {n : Nat} (c : Vector Float n) (m : Nat := 1) (scl : Float := 1.0) : 
    Id (Vector Float (n - min m n)) :=
  pure (hermder_aux c m scl)

-- LLM HELPER
lemma nat_toFloat_pos (n : Nat) : n > 0 → (n : Float) > 0 := by
  intro h
  sorry

-- LLM HELPER  
lemma hermder_aux_size {n : Nat} (c : Vector Float n) (m : Nat) (scl : Float) :
    (hermder_aux c m scl).size = n - min m n := by
  sorry

-- LLM HELPER
lemma hermder_step_spec {n : Nat} (c : Vector Float n) (scl : Float) (h : n > 0) :
    ∀ i : Fin (n - 1), 
      (hermder_step c scl).get ⟨i.val, sorry⟩ = 
      scl * (2.0 * (i.val + 1 : Nat).toFloat) * c.get ⟨i.val + 1, sorry⟩ := by
  sorry

/-- Specification: hermder differentiates Hermite series coefficients according to
    the Hermite polynomial derivative rule: d/dx H_n(x) = 2n * H_{n-1}(x).
    The result has degree reduced by m (or becomes zero if m >= n).
    Each differentiation multiplies by the scaling factor scl. -/
theorem hermder_spec {n : Nat} (c : Vector Float n) (m : Nat) (scl : Float) :
    ⦃⌜True⌝⦄
    hermder c m scl
    ⦃⇓result => ⌜
      -- Basic size property: output size is n - min(m, n)
      result.size = n - min m n ∧
      -- Case 1: Single differentiation (m = 1)
      (m = 1 ∧ n > 0 → 
        ∀ i : Fin (n - 1), 
          -- For Hermite polynomials: d/dx H_j(x) = 2j * H_{j-1}(x)
          -- So the i-th coefficient (degree i) comes from the (i+1)-th coefficient
          -- multiplied by 2*(i+1) and the scaling factor
          result.get ⟨i.val, sorry⟩ = scl * (2.0 * (i.val + 1 : Nat).toFloat) * c.get ⟨i.val + 1, sorry⟩) ∧
      -- Case 2: Over-differentiation (m ≥ n) gives empty vector
      (m ≥ n → result.size = 0) ∧
      -- Mathematical property: The operation reduces the degree by exactly m
      (m < n → result.size = n - m) ∧
      -- Mathematical property: Each differentiation applies the Hermite derivative rule
      -- For multiple differentiations, the pattern compounds
      (m = 2 ∧ n > 1 → 
        ∀ i : Fin (n - 2),
          -- Second derivative: apply the rule twice
          -- d²/dx² H_j(x) = d/dx (2j * H_{j-1}(x)) = 2j * 2(j-1) * H_{j-2}(x)
          result.get ⟨i.val, sorry⟩ = 
            scl * scl * (2.0 * (i.val + 2 : Nat).toFloat) * (2.0 * (i.val + 1 : Nat).toFloat) * 
            c.get ⟨i.val + 2, sorry⟩)
    ⌝⦄ := by
  simp [hermder]
  constructor
  · -- Basic size property
    exact hermder_aux_size c m scl
  constructor
  · -- Single differentiation case
    intro ⟨hm, hn⟩ i
    simp [hermder_aux, hm]
    exact hermder_step_spec c scl hn i
  constructor
  · -- Over-differentiation case
    intro h
    simp [hermder_aux_size]
    simp [min_def]
    split_ifs with h'
    · simp
    · contradiction
  constructor
  · -- Degree reduction property
    intro h
    simp [hermder_aux_size]
    simp [min_def]
    split_ifs with h'
    · contradiction
    · simp
  · -- Second derivative case
    intro ⟨hm, hn⟩ i
    simp [hermder_aux, hm]
    sorry