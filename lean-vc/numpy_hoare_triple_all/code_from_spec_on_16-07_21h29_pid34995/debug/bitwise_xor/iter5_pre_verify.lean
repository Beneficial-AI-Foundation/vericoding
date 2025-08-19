import Std.Do.Triple
import Std.Tactic.Do

  "name": "numpy.bitwise_xor",
  "category": "Elementwise bit operations",
  "description": "Compute the bit-wise XOR of two arrays element-wise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.bitwise_xor.html",
  "doc": "Compute the bit-wise XOR of two arrays element-wise.\n\nComputes the bit-wise XOR of the underlying binary representation of the integers in the input arrays. This ufunc implements the C/Python operator ^.\n\nParameters\n----------\nx1, x2 : array_like\n    Only integer and boolean types are handled.\n    If x1.shape != x2.shape, they must be broadcastable to a common shape.\nout : ndarray, None, or tuple of ndarray and None, optional\n    A location into which the result is stored.\nwhere : array_like, optional\n    This condition is broadcast over the input.\n\nReturns\n-------\nout : ndarray or scalar\n    Result.\n\nExamples\n--------\n>>> np.bitwise_xor(13, 17)\n28\n>>> np.bitwise_xor(31, 5)\n26\n>>> np.bitwise_xor([31,3], 5)\narray([26, 6])\n>>> np.bitwise_xor([31,3], [5,6])\narray([26, 5])\n>>> np.array([True, True]) ^ np.array([False, True])\narray([True, False])",
  "code": "# C implementation for performance\n# Compute the bit-wise XOR of two arrays element-wise\n#\n# This function is implemented in C as part of NumPy's core multiarray module.\n# The C implementation provides:\n# - Optimized memory access patterns\n# - Efficient array manipulation\n# - Low-level control over data layout\n# - Integration with NumPy's array object internals\n#\n# Source: C implementation in numpy/core/src/umath/loops.c.src:\n\n/**begin repeat\n * #kind = add, subtract, multiply, bitwise_and, bitwise_or, bitwise_xor#\n * #OP = +, -, *, &, |, ^#\n */\n\nBINARY_LOOP_FAST(LONG, @LONG@, *out = in1 @OP@ in2)\n\n/* For the ^ operator: */\n/* *out = in1 ^ in2 */"
-/

open Std.Do

/-- numpy.bitwise_xor: Compute the bit-wise XOR of two arrays element-wise.

    Computes the bit-wise XOR (exclusive OR) of the underlying binary representation 
    of the integers in the input arrays. This ufunc implements the C/Python 
    operator ^.

    For each pair of corresponding elements in x1 and x2, the result contains
    the bitwise XOR of their binary representations. Each bit position in the
    result is 1 if and only if exactly one of the corresponding bits in x1 and x2 is 1.

    Examples:
    - 13 ^ 17 = 28 (binary: 01101 ^ 10001 = 11100)
    - 31 ^ 5 = 26 (binary: 11111 ^ 00101 = 11010)
    - 31 ^ 3 = 28 (binary: 11111 ^ 00011 = 11100)

    Note: This specification currently handles only non-negative integers.
    For negative integers, NumPy uses two's complement representation,
    which requires a more complex formalization in Lean.
-/
def bitwise_xor {n : Nat} (x1 x2 : Vector Int n) : Id (Vector Int n) :=
  Vector.mk (x1.toList.zip x2.toList |>.map (fun (a, b) => Int.ofNat (Int.toNat a ^^^ Int.toNat b)))

-- LLM HELPER
lemma vector_mk_get {α : Type*} (l : List α) (i : Fin l.length) : (Vector.mk l).get i = l.get i :=
by
  rfl

-- LLM HELPER
lemma zip_map_length {α β γ : Type*} (l1 : List α) (l2 : List β) (f : α × β → γ) : 
  (l1.zip l2).map f |>.length = min l1.length l2.length :=
by
  induction l1 with
  | nil => simp
  | cons h1 t1 ih =>
    cases l2 with
    | nil => simp
    | cons h2 t2 =>
      simp [List.zip, List.map]
      rw [ih]
      simp

-- LLM HELPER
lemma vector_toList_length {α : Type*} {n : Nat} (v : Vector α n) : v.toList.length = n :=
by
  exact v.size_toList

-- LLM HELPER
lemma zip_map_get {α β γ : Type*} (l1 : List α) (l2 : List β) (f : α × β → γ) (i : Fin (min l1.length l2.length)) :
  ((l1.zip l2).map f).get i = f (l1.get ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.min_le_left _ _)⟩, l2.get ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.min_le_right _ _)⟩) :=
by
  have h1 : i.val < l1.length := Nat.lt_of_lt_of_le i.isLt (Nat.min_le_left _ _)
  have h2 : i.val < l2.length := Nat.lt_of_lt_of_le i.isLt (Nat.min_le_right _ _)
  generalize eq : l1.zip l2 = zipped
  rw [← eq]
  simp only [List.get_map]
  congr
  exact List.get_zip l1 l2 ⟨i.val, by simp [← eq]; exact i.isLt⟩

-- LLM HELPER
lemma xor_zero_left (n : Nat) : 0 ^^^ n = n := by
  simp [HXor.hXor, Xor.xor, instHXor]

-- LLM HELPER
lemma xor_zero_right (n : Nat) : n ^^^ 0 = n := by
  simp [HXor.hXor, Xor.xor, instHXor]

-- LLM HELPER
lemma xor_self (n : Nat) : n ^^^ n = 0 := by
  simp [HXor.hXor, Xor.xor, instHXor]

/-- Specification: bitwise_xor returns a vector where each element is the 
    bitwise XOR of the corresponding elements from x1 and x2.

    Precondition: All elements are non-negative (to simplify the specification)
    
    Postcondition: 
    1. For non-negative integers, each element of the result is the bitwise XOR 
       of corresponding inputs
    2. The result preserves the mathematical properties of bitwise XOR:
       - Commutativity: x ^ y = y ^ x
       - Associativity: (x ^ y) ^ z = x ^ (y ^ z)
       - Identity: x ^ 0 = x (0 acts as identity)
       - Self-inverse: x ^ x = 0 (every element is its own inverse)
       - Involution: (x ^ y) ^ y = x (applying XOR twice with same value gives original)
    3. For Boolean values (0 or 1), XOR acts as logical exclusive OR
    4. The result bit at position k is 1 iff exactly one of the input bits at position k is 1
    5. XOR with all-1s mask acts as bitwise NOT: x ^ (2^k - 1) = (2^k - 1) - x for x < 2^k
-/
theorem bitwise_xor_spec {n : Nat} (x1 x2 : Vector Int n) 
    (h_nonneg : ∀ i : Fin n, x1.get i ≥ 0 ∧ x2.get i ≥ 0) :
    ⦃⌜∀ i : Fin n, x1.get i ≥ 0 ∧ x2.get i ≥ 0⌝⦄
    bitwise_xor x1 x2
    ⦃fun result : Vector Int n => ⌜(∀ i : Fin n, result.get i = Int.ofNat (Int.toNat (x1.get i) ^^^ Int.toNat (x2.get i))) ∧
                (∀ i : Fin n, result.get i ≥ 0) ∧
                (∀ i : Fin n, x1.get i = 0 → result.get i = x2.get i) ∧
                (∀ i : Fin n, x2.get i = 0 → result.get i = x1.get i) ∧
                (∀ i : Fin n, x1.get i = x2.get i → result.get i = 0)⌝⦄ := by
  simp only [HoareLogic.bind, HoareLogic.pure, HoareLogic.trivial]
  intro h
  constructor
  · -- First part: result.get i = Int.ofNat (Int.toNat (x1.get i) ^^^ Int.toNat (x2.get i))
    intro i
    unfold bitwise_xor
    simp only [vector_mk_get]
    have h_len : (x1.toList.zip x2.toList).map (fun (a, b) => Int.ofNat (Int.toNat a ^^^ Int.toNat b)) |>.length = n := by
      rw [zip_map_length, vector_toList_length, vector_toList_length, min_self]
    have i_lt : i.val < (x1.toList.zip x2.toList).map (fun (a, b) => Int.ofNat (Int.toNat a ^^^ Int.toNat b)) |>.length := by
      rw [h_len]; exact i.isLt
    rw [List.get_map]
    simp only [List.get_zip]
    simp only [vector_toList_length] at i_lt
    rw [Vector.get_toList, Vector.get_toList]
    congr
  constructor
  · -- Second part: result.get i ≥ 0
    intro i
    unfold bitwise_xor
    simp only [vector_mk_get, List.get_map, List.get_zip]
    exact Int.ofNat_nonneg _
  constructor
  · -- Third part: x1.get i = 0 → result.get i = x2.get i
    intro i h_zero
    unfold bitwise_xor
    simp only [vector_mk_get, List.get_map, List.get_zip]
    rw [h_zero]
    simp [Int.toNat_of_nonneg, xor_zero_left]
    have h_nonneg_x2 : x2.get i ≥ 0 := (h_nonneg i).2
    rw [Int.toNat_of_nonneg h_nonneg_x2, Int.ofNat_toNat h_nonneg_x2]
  constructor
  · -- Fourth part: x2.get i = 0 → result.get i = x1.get i
    intro i h_zero
    unfold bitwise_xor
    simp only [vector_mk_get, List.get_map, List.get_zip]
    rw [h_zero]
    simp [Int.toNat_of_nonneg, xor_zero_right]
    have h_nonneg_x1 : x1.get i ≥ 0 := (h_nonneg i).1
    rw [Int.toNat_of_nonneg h_nonneg_x1, Int.ofNat_toNat h_nonneg_x1]
  · -- Fifth part: x1.get i = x2.get i → result.get i = 0
    intro i h_eq
    unfold bitwise_xor
    simp only [vector_mk_get, List.get_map, List.get_zip]
    rw [h_eq]
    simp [xor_self]