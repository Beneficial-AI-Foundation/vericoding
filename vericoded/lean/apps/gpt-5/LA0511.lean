import Mathlib
-- <vc-preamble>
def ValidInput (ab bc ca : Int) : Prop :=
  1 ≤ ab ∧ ab ≤ 100 ∧ 1 ≤ bc ∧ bc ≤ 100 ∧ 1 ≤ ca ∧ ca ≤ 100

def TriangleArea (ab bc : Int) : Int :=
  (ab * bc) / 2

def ValidArea (ab bc area : Int) : Prop :=
  ab ≥ 1 ∧ bc ≥ 1 ∧ area = TriangleArea ab bc ∧ area ≥ 0 ∧ area ≤ 5000

@[reducible, simp]
def solve_precond (ab bc ca : Int) : Prop :=
  ValidInput ab bc ca
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma zero_le_of_one_le {x : Int} (hx : 1 ≤ x) : 0 ≤ x :=
  le_trans (by decide) hx

-- LLM HELPER
lemma mul_nonneg_of_one_le {a b : Int} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    0 ≤ a * b :=
  mul_nonneg (zero_le_of_one_le ha) (zero_le_of_one_le hb)

-- LLM HELPER
lemma prod_le_10000_of_bounds {ab bc : Int}
    (hab1 : 1 ≤ ab) (hab100 : ab ≤ 100)
    (hbc1 : 1 ≤ bc) (hbc100 : bc ≤ 100) :
    ab * bc ≤ (100 : Int) * 100 := by
  have h0bc : 0 ≤ bc := zero_le_of_one_le hbc1
  have h0_100 : 0 ≤ (100 : Int) := by decide
  have h1 : ab * bc ≤ 100 * bc :=
    mul_le_mul_of_nonneg_right hab100 h0bc
  have h2 : 100 * bc ≤ 100 * 100 :=
    mul_le_mul_of_nonneg_left hbc100 h0_100
  exact le_trans h1 h2

-- LLM HELPER
lemma triangleArea_nonneg_of_bounds {ab bc : Int} (hab1 : 1 ≤ ab) (hbc1 : 1 ≤ bc) :
    0 ≤ TriangleArea ab bc := by
  have hmul : 0 ≤ ab * bc := mul_nonneg_of_one_le hab1 hbc1
  have h2_nonneg : 0 ≤ (2 : Int) := by decide
  simpa [TriangleArea] using Int.ediv_nonneg hmul h2_nonneg

-- LLM HELPER
lemma ediv_two_le_of_le_two_mul {z m : Int} (hle : z ≤ 2 * m) : z / 2 ≤ m := by
  have hz : 2 * (z / 2) + z % 2 = z := by simpa using Int.ediv_add_emod z 2
  have hnonneg : 0 ≤ z % 2 := Int.emod_nonneg z (by decide : (2 : Int) ≠ 0)
  have hmul_le : 2 * (z / 2) ≤ z := by
    have : 2 * (z / 2) ≤ 2 * (z / 2) + z % 2 := by
      simpa [two_mul] using add_le_add_left hnonneg (2 * (z / 2))
    simpa [hz] using this
  have htrans : 2 * (z / 2) ≤ 2 * m := le_trans hmul_le hle
  have h2pos : 0 < (2 : Int) := by decide
  exact le_of_mul_le_mul_left htrans h2pos

-- LLM HELPER
lemma triangleArea_le_5000_of_bounds {ab bc : Int}
    (hab1 : 1 ≤ ab) (hab100 : ab ≤ 100)
    (hbc1 : 1 ≤ bc) (hbc100 : bc ≤ 100) :
    TriangleArea ab bc ≤ 5000 := by
  have hprod_le : ab * bc ≤ (100 : Int) * 100 :=
    prod_le_10000_of_bounds hab1 hab100 hbc1 hbc100
  have hle : ab * bc ≤ 2 * ((100 : Int) * 50) := by
    have : 2 * ((100 : Int) * 50) = (100 : Int) * 100 := by decide
    simpa [this.symm] using hprod_le
  have hdiv_le : (ab * bc) / 2 ≤ (100 : Int) * 50 :=
    ediv_two_le_of_le_two_mul hle
  have : (100 : Int) * 50 = 5000 := by decide
  simpa [TriangleArea, this] using hdiv_le
-- </vc-helpers>

-- <vc-definitions>
def solve (ab bc ca : Int) (h_precond : solve_precond ab bc ca) : String :=
  let area := TriangleArea ab bc
  toString area ++ "\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (ab bc ca : Int) (result : String) (h_precond : solve_precond ab bc ca) : Prop :=
  ∃ area, ValidArea ab bc area ∧ result = toString area ++ "\n"

theorem solve_spec_satisfied (ab bc ca : Int) (h_precond : solve_precond ab bc ca) :
    solve_postcond ab bc ca (solve ab bc ca h_precond) h_precond := by
  rcases h_precond with ⟨hab1, hab100, hbc1, hbc100, _hca1, _hca100⟩
  refine ⟨TriangleArea ab bc, ?_, ?_⟩
  · refine And.intro hab1 (And.intro hbc1 (And.intro rfl (And.intro ?_ ?_)))
    · exact triangleArea_nonneg_of_bounds hab1 hbc1
    · exact triangleArea_le_5000_of_bounds hab1 hab100 hbc1 hbc100
  · simp [solve]
-- </vc-theorems>
