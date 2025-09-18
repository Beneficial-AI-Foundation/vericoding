-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_orthogonal (v1 v2 : List Int) : Bool := sorry

theorem nonzero_vector_not_self_orthogonal {v : List Int} 
  (h : ∃ x ∈ v, x ≠ 0) : ¬is_orthogonal v v := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem perpendicular_2d (n : Int) : 
  is_orthogonal [n, n] [-n, n] := sorry

theorem zero_vector_orthogonal {v : List Int} :
  let zeros := List.replicate v.length 0
  is_orthogonal v zeros ∧ is_orthogonal zeros v := sorry

theorem orthogonality_symmetric {v1 v2 : List Int} 
  (h : v1.length = v2.length) :
  is_orthogonal v1 v2 = is_orthogonal v2 v1 := sorry
-- </vc-theorems>