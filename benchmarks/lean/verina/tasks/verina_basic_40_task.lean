-- <vc-preamble>
@[reducible, simp]
def secondSmallest_precond (s : Array Int) : Prop :=
  s.size > 1
-- </vc-preamble>

-- <vc-helpers>
def minListHelper : List Int → Int
| [] => panic! "minListHelper: empty list"
| [_] => panic! "minListHelper: singleton list"
| a :: b :: [] => if a ≤ b then a else b
| a :: b :: c :: xs =>
    let m := minListHelper (b :: c :: xs)
    if a ≤ m then a else m

def minList (l : List Int) : Int :=
  minListHelper l

def secondSmallestAux (s : Array Int) (i minIdx secondIdx : Nat) : Int :=
  if i ≥ s.size then
    s[secondIdx]!
  else
    let x    := s[i]!
    let m    := s[minIdx]!
    let smin := s[secondIdx]!
    if x < m then
      secondSmallestAux s (i + 1) i minIdx
    else if x < smin then
      secondSmallestAux s (i + 1) minIdx i
    else
      secondSmallestAux s (i + 1) minIdx secondIdx
termination_by s.size - i
-- </vc-helpers>

-- <vc-definitions>
def secondSmallest (s : Array Int) (h_precond : secondSmallest_precond (s)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def secondSmallest_postcond (s : Array Int) (result: Int) (h_precond : secondSmallest_precond (s)) :=
  (∃ i, i < s.size ∧ s[i]! = result) ∧
  (∃ j, j < s.size ∧ s[j]! < result ∧
    ∀ k, k < s.size → s[k]! ≠ s[j]! → s[k]! ≥ result)

theorem secondSmallest_spec_satisfied (s: Array Int) (h_precond : secondSmallest_precond (s)) :
    secondSmallest_postcond (s) (secondSmallest (s) h_precond) h_precond := by
  sorry
-- </vc-theorems>