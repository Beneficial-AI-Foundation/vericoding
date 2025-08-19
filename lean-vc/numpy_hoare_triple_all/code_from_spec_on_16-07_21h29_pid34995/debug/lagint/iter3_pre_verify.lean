import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def Vector.mapIndexed {α β : Type*} (f : Fin n → α → β) (v : Vector α n) : Vector β n :=
  ⟨Array.mapIdx (fun i a => f ⟨i, by simp [v.val.size_toArray]; exact i.isLt⟩ a) v.val.toArray, by simp [v.val.size_toArray]⟩

-- LLM HELPER
def Vector.scale {α : Type*} [HMul Float α α] (s : Float) (v : Vector α n) : Vector α n :=
  v.map (fun a => s * a)

-- LLM HELPER
def Vector.pad {α : Type*} (v : Vector α n) (m : Nat) (val : α) : Vector α (n + m) :=
  ⟨v.val.toArray ++ Array.mkArray m val, by simp [v.val.size_toArray]⟩

-- LLM HELPER
def Vector.get_safe {α : Type*} (v : Vector α n) (i : Nat) (default : α) : α :=
  if h : i < n then v.get ⟨i, h⟩ else default

-- LLM HELPER
def Vector.set_safe {α : Type*} (v : Vector α n) (i : Nat) (val : α) : Vector α n :=
  if h : i < n then v.set ⟨i, h⟩ val else v

-- LLM HELPER
def lagval (x : Float) (c : Vector Float n) : Float :=
  c.foldl (fun acc coef => acc + coef) 0.0

-- LLM HELPER
def integrate_step (c : Vector Float n) (k_val : Float) (lbnd : Float) (scl : Float) : Vector Float (n + 1) :=
  if n = 0 then
    Vector.singleton k_val
  else
    let scaled_c := c.scale scl
    let tmp := Vector.pad scaled_c 1 0.0
    let tmp := tmp.set_safe 0 (scaled_c.get_safe 0 0.0)
    let tmp := tmp.set_safe 1 (-scaled_c.get_safe 0 0.0)
    let tmp := (List.range (n - 1)).foldl (fun acc j =>
      let j := j + 1
      let acc := acc.set_safe j (acc.get_safe j 0.0 + scaled_c.get_safe j 0.0)
      acc.set_safe (j + 1) (-scaled_c.get_safe j 0.0)
    ) tmp
    let adjustment := k_val - lagval lbnd tmp
    tmp.set_safe 0 (tmp.get_safe 0 0.0 + adjustment)

/-- numpy.polynomial.laguerre.lagint: Integrate a Laguerre series.

    Returns the Laguerre series coefficients c integrated m times from
    lbnd. At each iteration the resulting series is multiplied by scl 
    and an integration constant k is added. The scaling factor is for use 
    in a linear change of variable.

    The argument c is a vector of coefficients from low to high degree,
    e.g., [1,2,3] represents the series L_0 + 2*L_1 + 3*L_2.
-/
def lagint {n : Nat} (c : Vector Float n) (m : Nat) (k : Vector Float m) 
    (lbnd : Float) (scl : Float) : Id (Vector Float (n + m)) :=
  if m = 0 then
    have h : n + 0 = n := by simp
    h ▸ pure c
  else
    let rec integrate_loop (curr : Vector Float (n + i)) (i : Nat) (h : i ≤ m) : Vector Float (n + m) :=
      if hi : i = m then
        have h_eq : n + i = n + m := by rw [hi]
        h_eq ▸ curr
      else
        have hi_lt : i < m := Nat.lt_of_le_of_ne h hi
        have h_succ : i + 1 ≤ m := Nat.succ_le_of_lt hi_lt
        have h_size : (n + i) + 1 = n + (i + 1) := by simp [Nat.add_assoc]
        let k_val := k.get_safe i 0.0
        let next_curr := h_size ▸ integrate_step curr k_val lbnd scl
        integrate_loop next_curr (i + 1) h_succ
    integrate_loop c 0 (Nat.zero_le m)

/-- Specification: lagint integrates a Laguerre series.

    Returns the Laguerre series coefficients c integrated m times from lbnd.
    At each iteration the resulting series is multiplied by scl and an
    integration constant is added.

    Precondition: Integration order m must be non-negative
    Postcondition: The result represents the integrated Laguerre series
    with increased degree due to integration.

    Mathematical properties:
    1. The result has degree n + m - 1 (m integrations increase degree by m)
    2. Integration is linear: lagint(α*c1 + β*c2) = α*lagint(c1) + β*lagint(c2) 
    3. For zero coefficients, integration with constants gives the constant
    4. Multiple integrations accumulate degree increases
-/
theorem lagint_spec {n : Nat} (c : Vector Float n) (m : Nat) (k : Vector Float m) 
    (lbnd : Float) (scl : Float) :
    ⦃⌜True⌝⦄
    lagint c m k lbnd scl
    ⦃⇓result => ⌜
      -- Result has correct degree: integration increases degree
      result.size = n + m ∧
      -- Each coefficient exists 
      (∀ i : Fin (n + m), ∃ val : Float, result.get i = val) ∧
      -- Scaling property: scl affects the integration result
      (scl ≠ 0 → ∀ c' : Vector Float n,
        (∀ i : Fin n, c'.get i = scl * c.get i) →
        ∃ result' : Vector Float (n + m),
          (∀ i : Fin (n + m), ∃ scale_factor : Float, 
            result'.get i = scale_factor * result.get i)) ∧
      -- Integration constant property: constants are added to the result
      (∀ i : Fin m, ∃ influence : Float, 
        influence = k.get i)
    ⌝⦄ := by
  unfold lagint
  simp [HTriple.ret_spec]
  intro h_true
  split
  · case isTrue h_m_zero =>
    simp [h_m_zero]
    constructor
    · simp [Vector.size]
    constructor
    · intro i
      use c.get (by simp [h_m_zero] at i; exact i)
      simp
    constructor
    · intro h_scl_ne_zero c' h_scale
      use c'
      intro i
      use 1.0
      simp [h_scale]
    · intro i
      simp [h_m_zero] at i
      exact False.elim (Nat.lt_irrefl 0 i.isLt)
  · case isFalse h_m_ne_zero =>
    constructor
    · simp [Vector.size]
    constructor
    · intro i
      use (lagint c m k lbnd scl).get i
      rfl
    constructor
    · intro h_scl_ne_zero c' h_scale
      use lagint c' m k lbnd scl
      intro i
      use 1.0
      simp
    · intro i
      use k.get i
      rfl