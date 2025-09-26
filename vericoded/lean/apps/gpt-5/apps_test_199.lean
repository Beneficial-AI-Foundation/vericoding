import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) (s : Int) (v : List Int) : Prop :=
  n > 0 ∧ v.length = n ∧ s ≥ 0 ∧ ∀ i, 0 ≤ i ∧ i < v.length → v[i]! ≥ 0

def sum (v : List Int) : Int :=
  v.foldl (· + ·) 0

def minSeq (v : List Int) : Int :=
  if h : v.length > 0 then
    v.foldl min (v[0]!)
  else 0

def myMin (a : Int) (b : Int) : Int :=
  if a ≤ b then a else b

@[reducible, simp]
def solve_precond (n : Int) (s : Int) (v : List Int) : Prop :=
  ValidInput n s v
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma myMin_eq_left_of_le (a b : Int) (h : a ≤ b) : myMin a b = a := by
  simp [myMin, h]

-- LLM HELPER
lemma myMin_eq_right_of_gt (a b : Int) (h : b < a) : myMin a b = b := by
  have h' : ¬ a ≤ b := not_le.mpr h
  simp [myMin, h']

-- LLM HELPER
lemma myMin_nonneg_of_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ myMin a b := by
  by_cases h : a ≤ b
  · simpa [myMin, h] using ha
  · simpa [myMin, h] using hb

-- LLM HELPER
lemma min_nonneg_of_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ min a b := by
  by_cases h : a ≤ b
  · simpa [min_eq_left h] using ha
  · have h' : b ≤ a := le_of_lt (lt_of_not_ge h)
    simpa [min_eq_right h'] using hb

-- LLM HELPER
lemma foldl_min_nonneg_indexed_aux :
  ∀ (l : List Int),
    (∀ j, 0 ≤ j ∧ j < l.length → 0 ≤ l[j]!) →
    ∀ (a : Int), 0 ≤ a → 0 ≤ l.foldl min a
  | [], _, a, ha => by simpa [List.foldl] using ha
  | (z :: zs), hall, a, ha => by
      have hz : 0 ≤ z := by
        have hcond : 0 ≤ (0 : Nat) ∧ 0 < (z :: zs).length := ⟨Nat.zero_le _, by simp⟩
        simpa using hall 0 hcond
      have hall_zs : ∀ j, 0 ≤ j ∧ j < zs.length → 0 ≤ zs[j]! := by
        intro j hj
        have hj' : 0 ≤ j.succ ∧ j.succ < (z :: zs).length := by
          constructor
          · exact Nat.zero_le _
          · have : j.succ < zs.length.succ := Nat.succ_lt_succ hj.2
            simpa [List.length_cons] using this
        simpa using hall j.succ hj'
      have hmin_nonneg : 0 ≤ min a z := min_nonneg_of_nonneg a z ha hz
      have := foldl_min_nonneg_indexed_aux zs hall_zs (min a z) hmin_nonneg
      simpa [List.foldl] using this

-- LLM HELPER
lemma minSeq_nonneg_of_precond (n s : Int) (v : List Int) (h : ValidInput n s v) : 0 ≤ minSeq v := by
  classical
  rcases h with ⟨_, _, _, hall⟩
  by_cases hv : v.length > 0
  · have hx0 : 0 ≤ v[0]! := by
      have hcond : 0 ≤ (0 : Nat) ∧ 0 < v.length := ⟨Nat.zero_le _, hv⟩
      simpa using hall 0 hcond
    have hfold : 0 ≤ v.foldl min (v[0]!) :=
      foldl_min_nonneg_indexed_aux v (by
        intro j hj; simpa using hall j hj
      ) (v[0]!) hx0
    simpa [minSeq, hv] using hfold
  · simp [minSeq, hv]

-- LLM HELPER
lemma div_nonneg_of_nonneg_of_pos (a b : Int) (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  have hb' : 0 ≤ b := le_of_lt hb
  simpa using Int.ediv_nonneg ha hb'

-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (s : Int) (v : List Int) (h_precond : solve_precond n s v) : Int :=
  if h : sum v < s then -1 else myMin ((sum v - s) / n) (minSeq v)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (s : Int) (v : List Int) (result : Int) (h_precond : solve_precond n s v) : Prop :=
  (sum v < s → result = -1) ∧
  (sum v ≥ s → result = myMin ((sum v - s) / n) (minSeq v)) ∧
  (result = -1 ∨ result ≥ 0)

theorem solve_spec_satisfied (n : Int) (s : Int) (v : List Int) (h_precond : solve_precond n s v) :
    solve_postcond n s v (solve n s v h_precond) h_precond := by
  classical
rcases h_precond with ⟨hnpos, hlen_eq, hsnonneg, hall⟩
refine And.intro ?h1 (And.intro ?h2 ?h3)
· intro hlt
  simp [solve, hlt]
· intro hge
  have hnotlt : ¬ sum v < s := not_lt_of_ge hge
  simp [solve, hnotlt]
· by_cases hlt : sum v < s
  · left; simp [solve, hlt]
  · right
    have hge : s ≤ sum v := le_of_not_gt hlt
    have hnum_nonneg : 0 ≤ sum v - s := sub_nonneg.mpr hge
    have hdiv_nonneg : 0 ≤ (sum v - s) / n :=
      div_nonneg_of_nonneg_of_pos (sum v - s) n hnum_nonneg hnpos
    have hmin_nonneg : 0 ≤ minSeq v :=
      minSeq_nonneg_of_precond n s v ⟨hnpos, hlen_eq, hsnonneg, hall⟩
    have : 0 ≤ myMin ((sum v - s) / n) (minSeq v) :=
      myMin_nonneg_of_nonneg ((sum v - s) / n) (minSeq v) hdiv_nonneg hmin_nonneg
    simpa [solve, hlt] using this
-- </vc-theorems>
