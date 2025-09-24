-- <vc-preamble>
@[reducible, simp]
def stringXor_precond (a : Array Char) (b : Array Char) : Prop :=
  a.size = b.size ∧ 
  (∀ i, i < a.size → a[i]! = '0' ∨ a[i]! = '1') ∧
  (∀ i, i < b.size → b[i]! = '0' ∨ b[i]! = '1')
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def stringXor (a : Array Char) (b : Array Char) (h_precond : stringXor_precond a b) : Array Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def stringXor_postcond (a : Array Char) (b : Array Char) (result: Array Char) (h_precond : stringXor_precond a b) : Prop :=
  result.size = a.size ∧ 
  (∀ i, i < result.size → result[i]! = '0' ∨ result[i]! = '1') ∧
  (∀ i, i < result.size → result[i]! = (if a[i]! = b[i]! then '0' else '1'))

theorem stringXor_spec_satisfied (a: Array Char) (b: Array Char) (h_precond : stringXor_precond a b) :
    stringXor_postcond a b (stringXor a b h_precond) h_precond := by
  sorry
-- </vc-theorems>