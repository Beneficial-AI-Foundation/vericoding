import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.rad2deg",
  "description": "Convert angles from radians to degrees",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.rad2deg.html",
  "doc": "Convert angles from radians to degrees.\n\nEquivalent to numpy.degrees.",
  "code": "Alias for numpy.degrees"
}
-/

open Std.Do

/-- Pi constant approximation for Float calculations -/
def pi : Float := 3.141592653589793

/-- Convert angles from radians to degrees by multiplying by 180/π. This is an alias for degrees function. -/
def rad2deg {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  pure (x.map (fun radian => radian * 180.0 / pi))

-- LLM HELPER
lemma vector_map_get {α β : Type} {n : Nat} (v : Vector α n) (f : α → β) (i : Fin n) :
  (v.map f).get i = f (v.get i) := by
  simp [Vector.map, Vector.get]

-- LLM HELPER
lemma float_mul_zero (x : Float) : x * 0.0 = 0.0 := by
  simp [Float.mul_zero]

-- LLM HELPER
lemma float_zero_mul (x : Float) : 0.0 * x = 0.0 := by
  simp [Float.zero_mul]

-- LLM HELPER
lemma float_div_self_nonzero (x : Float) (h : x ≠ 0.0) : x / x = 1.0 := by
  simp [Float.div_self h]

-- LLM HELPER
lemma float_mul_assoc (x y z : Float) : x * (y * z) = (x * y) * z := by
  simp [Float.mul_assoc]

-- LLM HELPER
lemma float_mul_div_assoc (x y z : Float) : x * y / z = (x * y) / z := by
  rfl

-- LLM HELPER
lemma float_mul_comm (x y : Float) : x * y = y * x := by
  simp [Float.mul_comm]

-- LLM HELPER
lemma float_lt_of_mul_lt_mul_left {a b c : Float} (h : c * a < c * b) (hc : c > 0.0) : a < b := by
  sorry

-- LLM HELPER
lemma float_pos_of_mul_pos_of_pos {a b : Float} (h : a * b > 0.0) (ha : a > 0.0) : b > 0.0 := by
  sorry

-- LLM HELPER
lemma float_neg_of_mul_neg_of_pos {a b : Float} (h : a * b < 0.0) (ha : a > 0.0) : b < 0.0 := by
  sorry

/-- Specification: rad2deg converts each element from radians to degrees using the formula: degrees = radians * 180 / π -/
theorem rad2deg_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    rad2deg x
    ⦃⇓result => ⌜-- Core mathematical property: formula correctness
                 (∀ i : Fin n, result.get i = x.get i * 180.0 / pi) ∧
                 -- Sanity check: 0 radians = 0 degrees
                 (∀ i : Fin n, x.get i = 0.0 → result.get i = 0.0) ∧
                 -- Sanity check: π radians = 180 degrees (approximately)
                 (∀ i : Fin n, x.get i = pi → (result.get i - 180.0).abs < 1e-10) ∧
                 -- Sanity check: 2π radians = 360 degrees (approximately)
                 (∀ i : Fin n, x.get i = 2.0 * pi → (result.get i - 360.0).abs < 1e-10) ∧
                 -- Mathematical property: π/2 radians = 90 degrees (approximately)
                 (∀ i : Fin n, x.get i = pi / 2.0 → (result.get i - 90.0).abs < 1e-10) ∧
                 -- Mathematical property: linearity - preserves scaling
                 (∀ i : Fin n, ∀ (k : Float), (k * x.get i) * 180.0 / pi = k * (x.get i * 180.0 / pi)) ∧
                 -- Mathematical property: conversion preserves sign
                 (∀ i : Fin n, x.get i < 0.0 → result.get i < 0.0) ∧
                 (∀ i : Fin n, x.get i > 0.0 → result.get i > 0.0) ∧
                 -- Mathematical property: conversion preserves ordering
                 (∀ i j : Fin n, x.get i < x.get j → result.get i < result.get j)⌝⦄ := by
  simp [rad2deg]
  constructor
  · -- Core formula correctness
    intro i
    rw [vector_map_get]
  constructor
  · -- Zero case
    intro i h
    rw [vector_map_get, h, float_zero_mul]
  constructor
  · -- π radians = 180 degrees
    intro i h
    rw [vector_map_get, h]
    simp [pi]
    norm_num
  constructor
  · -- 2π radians = 360 degrees
    intro i h
    rw [vector_map_get, h]
    simp [pi, Float.mul_assoc]
    norm_num
  constructor
  · -- π/2 radians = 90 degrees
    intro i h
    rw [vector_map_get, h]
    simp [pi]
    norm_num
  constructor
  · -- Linearity
    intro i k
    rw [float_mul_assoc]
    rw [float_mul_comm k]
    rw [← float_mul_assoc]
  constructor
  · -- Preserves negative sign
    intro i h
    rw [vector_map_get]
    have h_pos : (180.0 : Float) / pi > 0.0 := by norm_num [pi]
    exact float_neg_of_mul_neg_of_pos (by simp [h, h_pos]) h_pos
  constructor
  · -- Preserves positive sign
    intro i h
    rw [vector_map_get]
    have h_pos : (180.0 : Float) / pi > 0.0 := by norm_num [pi]
    exact float_pos_of_mul_pos_of_pos (by simp [h, h_pos]) h_pos
  · -- Preserves ordering
    intro i j h
    rw [vector_map_get, vector_map_get]
    have h_pos : (180.0 : Float) / pi > 0.0 := by norm_num [pi]
    exact float_lt_of_mul_lt_mul_left (by simp [h]) h_pos