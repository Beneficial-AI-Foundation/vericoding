-- <vc-preamble>
/-!
{
  "name": "numpy.nonzero",
  "category": "Boolean/mask indexing",
  "description": "Return the indices of the elements that are non-zero",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.nonzero.html",
  "doc": "Return the indices of the elements that are non-zero.\n\nReturns a tuple of arrays, one for each dimension of `a`, containing the indices of the non-zero elements in that dimension. The values in `a` are always tested and returned in row-major, C-style order.\n\nParameters\n----------\na : array_like\n    Input array.\n\nReturns\n-------\ntuple_of_arrays : tuple\n    Indices of elements that are non-zero.",
  "code": "@array_function_dispatch(_nonzero_dispatcher)\ndef nonzero(a):\n    \"\"\"\n    Return the indices of the elements that are non-zero.\n\n    Returns a tuple of arrays, one for each dimension of `a`,\n    containing the indices of the non-zero elements in that\n    dimension. The values in `a` are always tested and returned in\n    row-major, C-style order.\n\n    Parameters\n    ----------\n    a : array_like\n        Input array.\n\n    Returns\n    -------\n    tuple_of_arrays : tuple\n        Indices of elements that are non-zero.\n    \"\"\"\n    return _wrapfunc(a, 'nonzero')"
}
-/

/-- numpy.nonzero: Return the indices of the elements that are non-zero.
    
    For a 1D array, returns a list containing the indices of all non-zero elements.
    The indices are returned in ascending order and correspond to positions where
    the input array has non-zero values.
    
    This function is commonly used for boolean indexing and finding positions
    of elements that satisfy certain conditions.
-/
def nonzero {n : Nat} (a : Vector Float n) : List (Fin n) :=
  sorry

/-- Helper: Check if a vector is the zero vector -/
def is_zero_vector {n : Nat} (a : Vector Float n) : Prop :=
  ∀ i : Fin n, a.get i = 0

/-- Helper: Count non-zero elements in a vector -/
def count_nonzero {n : Nat} (a : Vector Float n) : Nat :=
  sorry

/-- Specification: nonzero returns exactly the indices of non-zero elements.
    
    The returned list contains all and only the indices where the input array
    has non-zero values. The indices are returned in ascending order.
    
    Key properties:
    1. Correctness: Every index in result points to a non-zero element
    2. Completeness: Every non-zero element is represented in the result
    3. Ordering: Results are sorted in ascending order
    4. Uniqueness: No duplicates in the result
    5. Boundedness: Result length is at most the input array length
-/
theorem nonzero_spec {n : Nat} (a : Vector Float n) :
    let result := nonzero a
    -- 1. Correctness: All indices in result point to non-zero elements
    (∀ i ∈ result, a.get i ≠ 0) ∧
    -- 2. Completeness: All non-zero elements are represented in result
    (∀ j : Fin n, a.get j ≠ 0 → j ∈ result) ∧
    -- 3. Ordering: The result is sorted in ascending order
    (List.Pairwise (· < ·) result) ∧
    -- 4. Uniqueness: No duplicates in result
    (result.Nodup) ∧
    -- 5. Boundedness: Result length is at most input length
    (result.length ≤ n) ∧
    -- 6. Length relationship: Result length equals count of non-zero elements
    (result.length = count_nonzero a) := by
  sorry

/-- Empty result characterization: nonzero returns empty list iff input is zero vector -/
theorem nonzero_empty_iff_zero {n : Nat} (a : Vector Float n) :
    nonzero a = [] ↔ is_zero_vector a := by
  sorry

/-- Full result characterization: nonzero returns all indices iff no element is zero -/
theorem nonzero_full_iff_no_zeros {n : Nat} (a : Vector Float n) :
    (nonzero a).length = n ↔ (∀ i : Fin n, a.get i ≠ 0) := by
  sorry

/-- Monotonicity: If we zero out some elements, the result is a subset -/
theorem nonzero_monotonic {n : Nat} (a b : Vector Float n) :
    (∀ i : Fin n, a.get i ≠ 0 → b.get i ≠ 0) →
    ∀ x ∈ nonzero a, x ∈ nonzero b := by
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>