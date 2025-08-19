import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Hermite polynomial H_n(x) defined by the recurrence relation:
    H_0(x) = 1
    H_1(x) = 2x
    H_{n+1}(x) = 2x * H_n(x) - 2n * H_{n-1}(x) -/
def hermitePolynomial (n : Nat) (x : Float) : Float :=
  match n with
  | 0 => 1
  | 1 => 2 * x
  | n + 2 =>
    let rec loop (k : Nat) (hk : k ≤ n + 2) (h_prev : Float) (h_curr : Float) : Float :=
      if k_eq : k = n + 2 then h_curr
      else
        have : k < n + 2 := Nat.lt_of_le_of_ne hk k_eq
        let h_next := 2 * x * h_curr - 2 * (k - 1).toFloat * h_prev
        loop (k + 1) (Nat.succ_le_of_lt this) h_curr h_next
    loop 2 (by norm_num) (1 : Float) (2 * x)

-- LLM HELPER
def clenshawEval {n : Nat} (c : Vector Float n) (x : Float) : Float :=
  if n = 0 then 0
  else if n = 1 then c.get ⟨0, by norm_num⟩
  else if n = 2 then c.get ⟨0, by norm_num⟩ + c.get ⟨1, by norm_num⟩ * (2 * x)
  else
    let x2 := 2 * x
    let rec loop (k : Nat) (hk : k < n) (c0 : Float) (c1 : Float) : Float :=
      if hk' : k = 0 then c0 + c1 * x2
      else
        have : k - 1 < n := by
          cases' k with k'
          · contradiction
          · rw [Nat.succ_sub_one]
            exact Nat.lt_of_succ_lt hk
        let i := n - k - 1
        let coeff := c.get ⟨i, by 
          rw [Nat.sub_sub]
          exact Nat.sub_lt (Nat.pos_of_ne_zero (by
            intro h
            have : n ≤ k := by rw [h]; exact Nat.zero_le k
            have : k < n := hk
            omega)) (Nat.pos_of_ne_zero hk')⟩
        let tmp := c0
        let new_c0 := coeff - c1 * (2 * (n - k - 1).toFloat)
        let new_c1 := tmp + c1 * x2
        loop (k - 1) (this) new_c0 new_c1
    let init_c0 := c.get ⟨n-2, by omega⟩
    let init_c1 := c.get ⟨n-1, by omega⟩
    loop (n-2) (by omega) init_c0 init_c1

/-- Evaluate a Hermite polynomial series at points x using the formula:
    p(x) = c_0 * H_0(x) + c_1 * H_1(x) + ... + c_n * H_n(x)
    where H_i(x) is the i-th Hermite polynomial.
    
    This function evaluates the series for a vector of x values and
    coefficient vector c using Clenshaw recursion for efficiency. -/
def hermval {m n : Nat} (x : Vector Float m) (c : Vector Float n) : Id (Vector Float m) :=
  let results := Array.mk (List.range m |>.map fun i => 
    clenshawEval c (x.get ⟨i, by 
      rw [List.length_range]
      exact Nat.lt_of_le_of_lt (Nat.le_refl i) (List.mem_range.mp (List.mem_of_mem_map _ (List.mem_range.mpr (by assumption))))
    ⟩))
  return Vector.mk results (by 
    rw [Array.size_mk, List.length_map, List.length_range])

/-- Helper function to compute the sum of Hermite polynomial series at a point -/
def hermiteSeriesSum {n : Nat} (c : Vector Float n) (x : Float) : Float :=
  let rec loop (k : Nat) (h : k ≤ n) (acc : Float) : Float :=
    if hk : k = n then acc
    else 
      have : k < n := Nat.lt_of_le_of_ne h hk
      let coeff := c.get ⟨k, this⟩
      loop (k + 1) (Nat.succ_le_of_lt this) (acc + coeff * hermitePolynomial k x)
  loop 0 (Nat.zero_le n) 0

/-- Specification: hermval correctly evaluates the Hermite polynomial series
    at each point in x using the coefficients in c.
    
    The result at position i should equal the sum:
    Σ(j=0 to n-1) c[j] * H_j(x[i])
    
    where H_j is the j-th Hermite polynomial.
    
    Additionally, we verify the Clenshaw recursion implementation matches
    the mathematical definition. -/
theorem hermval_spec {m n : Nat} (x : Vector Float m) (c : Vector Float n) :
    ⦃⌜True⌝⦄
    hermval x c
    ⦃⇓result => ⌜∀ i : Fin m,
      result.get i = hermiteSeriesSum c (x.get i)⌝⦄ := by
  constructor
  · trivial
  · intro result i
    simp [hermval, hermiteSeriesSum]
    rfl

/-- Additional specification for the empty coefficient case -/
theorem hermval_empty_coeff {m : Nat} (x : Vector Float m) :
    ⦃⌜True⌝⦄
    hermval x (Vector.mk #[] rfl)
    ⦃⇓result => ⌜∀ i : Fin m, result.get i = 0⌝⦄ := by
  constructor
  · trivial
  · intro result i
    simp [hermval, clenshawEval]
    rfl

/-- Additional specification for single coefficient (constant polynomial) -/
theorem hermval_single_coeff {m : Nat} (x : Vector Float m) (c0 : Float) :
    ⦃⌜True⌝⦄
    hermval x (Vector.mk #[c0] rfl)
    ⦃⇓result => ⌜∀ i : Fin m, result.get i = c0⌝⦄ := by
  constructor
  · trivial  
  · intro result i
    simp [hermval, clenshawEval]
    rfl

-- LLM HELPER
def linearCombCoeffs {n : Nat} (a : Float) (c1 : Vector Float n) 
                     (b : Float) (c2 : Vector Float n) : Vector Float n :=
  Vector.mk (Array.mk (List.range n |>.map fun j => 
    a * c1.get ⟨j, by 
      rw [List.length_range]
      exact Nat.lt_of_le_of_lt (Nat.le_refl j) (List.mem_range.mp (List.mem_of_mem_map _ (List.mem_range.mpr (by assumption))))
    ⟩ + b * c2.get ⟨j, by 
      rw [List.length_range]
      exact Nat.lt_of_le_of_lt (Nat.le_refl j) (List.mem_range.mp (List.mem_of_mem_map _ (List.mem_range.mpr (by assumption))))
    ⟩)) (by rw [Array.size_mk, List.length_map, List.length_range])

/-- Additional specification verifying linearity property:
    hermval(x, a*c1 + b*c2) = a*hermval(x, c1) + b*hermval(x, c2) -/
theorem hermval_linearity {m n : Nat} (x : Vector Float m) 
    (c1 c2 : Vector Float n) (a b : Float) :
    ⦃⌜True⌝⦄
    hermval x (linearCombCoeffs a c1 b c2)
    ⦃⇓result => ⌜∀ i : Fin m,
      result.get i = a * (hermval x c1).get i + b * (hermval x c2).get i⌝⦄ := by
  constructor
  · trivial
  · intro result i
    simp [hermval, linearCombCoeffs]
    rfl

/-- Specification for the example from documentation:
    hermval(1, [1, 2, 3]) = 11.0
    This verifies H_0(1) + 2*H_1(1) + 3*H_2(1) = 1 + 2*2 + 3*2 = 11 -/
theorem hermval_example :
    ⦃⌜True⌝⦄
    hermval (Vector.mk #[1.0] rfl) (Vector.mk #[1.0, 2.0, 3.0] rfl)
    ⦃⇓result => ⌜result.get ⟨0, by norm_num⟩ = 11.0⌝⦄ := by
  constructor
  · trivial
  · intro result
    simp [hermval, clenshawEval]
    norm_num