import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  n ≥ 1

def MinBills (n : Int) : Int :=
  n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5)

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma minbills_nonneg (n : Int) (h : n ≥ 1) : MinBills n ≥ 0 := by
  unfold MinBills
  have h100_pos : (0 : Int) ≤ 100 := by norm_num
  have h20_pos : (0 : Int) ≤ 20 := by norm_num
  have h10_pos : (0 : Int) ≤ 10 := by norm_num
  have h5_pos : (0 : Int) ≤ 5 := by norm_num
  have h100_ne : (100 : Int) ≠ 0 := by norm_num
  have h20_ne : (20 : Int) ≠ 0 := by norm_num
  have h10_ne : (10 : Int) ≠ 0 := by norm_num
  have h5_ne : (5 : Int) ≠ 0 := by norm_num
  have hn_nonneg : n ≥ 0 := by omega
  have h1 : n / 100 ≥ 0 := Int.ediv_nonneg hn_nonneg h100_pos
  have h2 : (n % 100) / 20 ≥ 0 := Int.ediv_nonneg (Int.emod_nonneg n h100_ne) h20_pos
  have h3 : ((n % 100) % 20) / 10 ≥ 0 := Int.ediv_nonneg (Int.emod_nonneg _ h20_ne) h10_pos
  have h4 : (((n % 100) % 20) % 10) / 5 ≥ 0 := Int.ediv_nonneg (Int.emod_nonneg _ h10_ne) h5_pos
  have h5 : ((((n % 100) % 20) % 10) % 5) ≥ 0 := Int.emod_nonneg _ h5_ne
  omega
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  MinBills n
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : Int) (h_precond : solve_precond n) : Prop :=
  result ≥ 0 ∧ result = MinBills n

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · exact minbills_nonneg n h_precond
  · rfl
-- </vc-theorems>
