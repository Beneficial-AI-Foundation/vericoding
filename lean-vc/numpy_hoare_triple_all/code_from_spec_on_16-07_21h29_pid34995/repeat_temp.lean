import Std.Do.Triple
import Std.Tactic.Do
import Init.Data.Vector.Basic

open Std.Do

/-!
{
  "name": "numpy.repeat",
  "category": "Tiling Arrays",
  "description": "Repeat elements of an array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.repeat.html",
  "doc": "Repeat elements of an array.\n\nParameters\n----------\na : array_like\n    Input array.\nrepeats : int or array of ints\n    The number of repetitions for each element. \`repeats\` is broadcasted\n    to fit the shape of the given axis.\naxis : int, optional\n    The axis along which to repeat values. By default, use the\n    flattened input array, and return a flat output array.\n\nReturns\n-------\nrepeated_array : ndarray\n    Output array which has the same shape as \`a\`, except along\n    the given axis.\n\nExamples\n--------\n>>> np.repeat(3, 4)\narray([3, 3, 3, 3])\n>>> x = np.array([[1,2],[3,4]])\n>>> np.repeat(x, 2)\narray([1, 1, 2, 2, 3, 3, 4, 4])\n>>> np.repeat(x, 3, axis=1)\narray([[1, 1, 1, 2, 2, 2],\n       [3, 3, 3, 4, 4, 4]])\n>>> np.repeat(x, [1, 2], axis=0)\narray([[1, 2],\n       [3, 4],\n       [3, 4]])",
  "code": "# Implementation in numpy/_core/fromnumeric.py\n# See NumPy source code repository",
  "source_location": "numpy/_core/fromnumeric.py",
  "signature": "numpy.repeat(a, repeats, axis=None)"
}
-/

-- LLM HELPER
def repeatAux {α : Type} {n : Nat} (a : Vector α n) (repeats : Nat) : List α :=
  List.flatten (List.map (fun i => List.replicate repeats (a.get ⟨i, List.mem_range.mp (List.mem_range.mpr i.isLt)⟩)) (List.range n))

-- LLM HELPER
theorem sum_map_length_replicate (n repeats : Nat) (f : Fin n → α) :
    (List.map (fun i => List.replicate repeats (f ⟨i, List.mem_range.mp (List.mem_range.mpr i.isLt)⟩)) (List.range n)).map List.length = List.replicate n repeats := by
  simp [List.map_map, List.length_replicate]
  rw [List.map_const]

-- LLM HELPER
theorem repeatAux_length {α : Type} {n : Nat} (a : Vector α n) (repeats : Nat) :
    (repeatAux a repeats).length = n * repeats := by
  unfold repeatAux
  rw [List.length_flatten]
  simp [List.map_map]
  have h : (List.map (fun i => List.replicate repeats (a.get ⟨i, List.mem_range.mp (List.mem_range.mpr i.isLt)⟩)) (List.range n)).map List.length = List.replicate n repeats := by
    apply sum_map_length_replicate
  rw [h, List.sum_replicate, List.length_range]

/-- Repeat elements of a vector a specified number of times.
    Each element is repeated consecutively. -/
def «repeat» {α : Type} {n : Nat} (a : Vector α n) (repeats : Nat) : Id (Vector α (n * repeats)) :=
  pure ⟨(repeatAux a repeats).toArray, by rw [List.size_toArray, repeatAux_length]⟩

-- LLM HELPER
theorem div_lt_of_lt_mul {a b c : Nat} (h : a < b * c) (hc : c > 0) : a / c < b := by
  exact Nat.div_lt_iff_lt_mul_right hc.ne' ▸ h

-- LLM HELPER
theorem get_repeatAux {α : Type} {n : Nat} (a : Vector α n) (repeats : Nat) (i : Fin (n * repeats)) :
    ∃ (k : Fin n), i.val / repeats = k.val ∧ (repeatAux a repeats).get ⟨i.val, by rw [repeatAux_length]; exact i.isLt⟩ = a.get k := by
  cases' repeats with repeats
  · simp [Nat.mul_zero] at i
    exact Fin.elim0 i
  · have hr_pos : repeats.succ > 0 := Nat.zero_lt_succ _
    have k_val := i.val / repeats.succ
    have k_lt : k_val < n := div_lt_of_lt_mul i.isLt hr_pos
    use ⟨k_val, k_lt⟩
    constructor
    · rfl
    · unfold repeatAux
      simp [List.get_flatten, List.map_map]
      rw [List.get_map, List.get_range]
      simp [List.get_replicate]
      rfl

-- LLM HELPER
theorem add_lt_mul_succ {a b c : Nat} (ha : a < b) (hc : c < b.succ) : a * b.succ + c < b * b.succ := by
  rw [Nat.mul_comm b]
  have h1 : a * b.succ + c < (a + 1) * b.succ := by
    rw [Nat.add_mul]
    simp [Nat.one_mul]
    exact Nat.add_lt_add_left hc (a * b.succ)
  have h2 : (a + 1) * b.succ ≤ b * b.succ := by
    rw [Nat.mul_comm (a + 1), Nat.mul_comm b]
    exact Nat.mul_le_mul_left b.succ (Nat.succ_le_iff.mpr ha)
  exact Nat.lt_of_lt_of_le h1 h2

-- LLM HELPER
theorem exists_idx_for_repeat {α : Type} {n : Nat} (a : Vector α n) (repeats : Nat) (k : Fin n) (j : Fin repeats) :
    ∃ (idx : Fin (n * repeats)), idx.val = k.val * repeats + j.val ∧ 
    (repeatAux a repeats).get ⟨idx.val, by rw [repeatAux_length]; exact idx.isLt⟩ = a.get k := by
  have idx_val := k.val * repeats + j.val
  have idx_lt : idx_val < n * repeats := by
    rw [Nat.mul_comm]
    exact Nat.add_lt_mul j.isLt k.isLt
  use ⟨idx_val, idx_lt⟩
  constructor
  · rfl
  · unfold repeatAux
    simp [List.get_flatten, List.map_map]
    rw [List.get_map, List.get_range]
    simp [List.get_replicate]
    rfl

/-- Specification: repeat creates a vector where each element from the input 
    appears consecutively 'repeats' times. The resulting vector has size n * repeats.
    
    For a vector [a₀, a₁, ..., aₙ₋₁] and repeats = r, the result is:
    [a₀, a₀, ..., a₀, a₁, a₁, ..., a₁, ..., aₙ₋₁, aₙ₋₁, ..., aₙ₋₁]
     \___r times___/  \___r times___/       \______r times______/
     
    Mathematical properties:
    1. Each element appears exactly 'repeats' times consecutively
    2. The total size is n * repeats
    3. Element at index i comes from input element at index ⌊i/repeats⌋
    4. Elements are grouped: positions [k*repeats, (k+1)*repeats) contain a[k]
-/
theorem repeat_spec {α : Type} {n : Nat} (a : Vector α n) (repeats : Nat) (h_pos : repeats > 0) :
    ⦃⌜repeats > 0⌝⦄
    «repeat» a repeats
    ⦃⇓result => ⌜(∀ i : Fin (n * repeats), 
                   ∃ (k : Fin n), 
                     i.val / repeats = k.val ∧ 
                     result.get i = a.get k) ∧
                  (∀ k : Fin n, ∀ j : Fin repeats,
                   ∃ (idx : Fin (n * repeats)),
                     idx.val = k.val * repeats + j.val ∧
                     result.get idx = a.get k)⌝⦄ := by
  simp [Std.Do.triple_simp]
  constructor
  · intro i
    have h1 := get_repeatAux a repeats i
    obtain ⟨k, hk1, hk2⟩ := h1
    use k
    constructor
    · exact hk1
    · simp [«repeat»]
      rw [←List.get_toArray]
      exact hk2
  · intro k j
    have h1 := exists_idx_for_repeat a repeats k j
    obtain ⟨idx, hidx1, hidx2⟩ := h1
    use idx
    constructor
    · exact hidx1
    · simp [«repeat»]
      rw [←List.get_toArray]
      exact hidx2