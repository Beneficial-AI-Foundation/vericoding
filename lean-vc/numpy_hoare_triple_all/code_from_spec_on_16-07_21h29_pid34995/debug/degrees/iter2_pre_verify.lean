import Std.Do.Triple
import Std.Tactic.Do

  "name": "numpy.degrees",
  "description": "Convert angles from radians to degrees",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.degrees.html",
  "doc": "Convert angles from radians to degrees.\n\nSignature: numpy.degrees(x, /, out=None, *, where=True, casting='same_kind', order='K', dtype=None, subok=True)\n\nParameters:\n  x: array_like - Input array in radians\n\nReturns:\n  y: ndarray - The corresponding degree values",
  "code": "Implemented as x * 180 / pi"
-/

open Std.Do

/-- Pi constant approximation for Float calculations -/
def pi : Float := 3.141592653589793

/-- Convert angles from radians to degrees by multiplying by 180/π -/
def degrees {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  pure (x.map (fun radian => radian * 180.0 / pi))

-- LLM HELPER
lemma vector_map_get {α β : Type*} {n : Nat} (v : Vector α n) (f : α → β) (i : Fin n) :
  (v.map f).get i = f (v.get i) := by
  rfl

-- LLM HELPER
lemma float_mul_assoc (a b c : Float) : a * b * c = a * (b * c) := by
  ring

-- LLM HELPER
lemma float_div_mul_cancel (a b : Float) (h : b ≠ 0) : a / b * b = a := by
  rw [div_mul_cancel a h]

-- LLM HELPER
lemma float_zero_mul (a : Float) : 0.0 * a = 0.0 := by
  ring

-- LLM HELPER  
lemma float_mul_div_assoc (a b c : Float) : a * b / c = a * (b / c) := by
  ring

-- LLM HELPER
lemma float_neg_mul (a b : Float) : (-a) * b = -(a * b) := by
  ring

-- LLM HELPER
lemma float_mul_pos {a b : Float} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  exact mul_pos ha hb

-- LLM HELPER
lemma float_mul_neg {a b : Float} (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  exact mul_neg_of_neg_of_pos ha hb

-- LLM HELPER
lemma float_mul_lt_mul_of_pos_right {a b c : Float} (h : a < b) (hc : 0 < c) : a * c < b * c := by
  exact mul_lt_mul_of_pos_right h hc

/-- Specification: degrees converts each element from radians to degrees using the formula: degrees = radians * 180 / π -/
theorem degrees_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    degrees x
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
  simp [degrees]
  constructor
  · -- Core formula correctness
    intro i
    rw [vector_map_get]
  constructor
  · -- 0 radians = 0 degrees
    intro i h
    rw [vector_map_get, h, float_zero_mul]
  constructor
  · -- π radians = 180 degrees (approximately)
    intro i h
    rw [vector_map_get, h]
    simp [pi]
    norm_num
  constructor
  · -- 2π radians = 360 degrees (approximately)
    intro i h
    rw [vector_map_get, h]
    simp [pi]
    norm_num
  constructor
  · -- π/2 radians = 90 degrees (approximately)
    intro i h
    rw [vector_map_get, h]
    simp [pi]
    norm_num
  constructor
  · -- Linearity - preserves scaling
    intro i k
    rw [float_mul_div_assoc, float_mul_assoc]
  constructor
  · -- Conversion preserves negative sign
    intro i h
    rw [vector_map_get]
    have h_pos : (0 : Float) < 180.0 / pi := by norm_num [pi]
    exact float_mul_neg h h_pos
  constructor
  · -- Conversion preserves positive sign
    intro i h
    rw [vector_map_get]
    have h_pos : (0 : Float) < 180.0 / pi := by norm_num [pi]
    exact float_mul_pos h h_pos
  · -- Conversion preserves ordering
    intro i j h
    rw [vector_map_get, vector_map_get]
    have h_pos : (0 : Float) < 180.0 / pi := by norm_num [pi]
    exact float_mul_lt_mul_of_pos_right h h_pos