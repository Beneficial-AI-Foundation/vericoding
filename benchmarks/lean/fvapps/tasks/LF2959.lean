-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def distribute (m n: Int) : List Int := sorry

def sum : List Int → Int
  | [] => 0
  | x::xs => x + sum xs
-- </vc-definitions>

-- <vc-theorems>
theorem nonpositive_n_returns_empty {m n : Int} (h: n ≤ 0) : 
  distribute m n = [] := sorry

theorem nonpositive_m_distributes_zeros {m n : Int} (h₁: m ≤ 0) (h₂: n > 0) :
  let result := distribute m n
  (result.length = n) ∧ (∀ x ∈ result, x = 0) := sorry

theorem distribution_properties {m n : Int} (h₁: m ≥ 0) (h₂: n > 0) :
  let result := distribute m n
  (result.length = n) ∧ 
  (sum result = m) ∧
  (∀ i j, i < result.length → j < result.length → 
    (result.get ⟨i, by sorry⟩ - result.get ⟨j, by sorry⟩ ≤ 1 ∧ 
     result.get ⟨j, by sorry⟩ - result.get ⟨i, by sorry⟩ ≤ 1)) ∧
  (∀ i, i < result.length - 1 → 
    result.get ⟨i, by sorry⟩ ≥ result.get ⟨i+1, by sorry⟩) := sorry
-- </vc-theorems>