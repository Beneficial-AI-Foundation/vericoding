/-
Suppose I have two vectors: `(a1, a2, a3, ..., aN)` and `(b1, b2, b3, ..., bN)`. The dot product between these two vectors is defined as:

```
a1*b1 + a2*b2 + a3*b3 + ... + aN*bN
```

The vectors are classified as orthogonal if the dot product equals zero.

Complete the function that accepts two sequences as inputs and returns `true` if the vectors are orthogonal, and `false` if they are not. The sequences will always be correctly formatted and of the same length, so there is no need to check them first.

## Examples
```
[1, 1, 1], [2, 5, 7]        --> false
[1, 0, 0, 1], [0, 1, 1, 0]  --> true
```
-/

-- <vc-helpers>
-- </vc-helpers>

def is_orthogonal (v1 v2 : List Int) : Bool := sorry

theorem nonzero_vector_not_self_orthogonal {v : List Int} 
  (h : ∃ x ∈ v, x ≠ 0) : ¬is_orthogonal v v := sorry

theorem perpendicular_2d (n : Int) : 
  is_orthogonal [n, n] [-n, n] := sorry

theorem zero_vector_orthogonal {v : List Int} :
  let zeros := List.replicate v.length 0
  is_orthogonal v zeros ∧ is_orthogonal zeros v := sorry

theorem orthogonality_symmetric {v1 v2 : List Int} 
  (h : v1.length = v2.length) :
  is_orthogonal v1 v2 = is_orthogonal v2 v1 := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_orthogonal [1, -2] [2, 1]

/-
info: True
-/
-- #guard_msgs in
-- #eval is_orthogonal [1, 2, 3] [0, -3, 2]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_orthogonal [1, 1, 1] [2, 5, 7]

-- Apps difficulty: introductory
-- Assurance level: unguarded