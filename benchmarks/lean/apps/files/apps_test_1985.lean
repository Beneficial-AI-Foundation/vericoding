-- <vc-preamble>
def sum (s : List Int) : Int :=
  match s with
  | [] => 0
  | h :: t => h + sum t

def computeInitialScore (pos : Int) (a : List Int) (b : List Int) : Int :=
  b[0]! - sum (a.take (pos.toNat + 1))

partial def computeBackwardScores (pos : Int) (scoreAtPos : Int) (a : List Int) : List Int :=
  if pos = 0 then [scoreAtPos]
  else scoreAtPos :: computeBackwardScores (pos - 1) (scoreAtPos - a[pos.toNat]!) a

partial def computeForwardScores (pos : Int) (scoreAtPos : Int) (a : List Int) : List Int :=
  if pos = a.length - 1 then []
  else (scoreAtPos + a[(pos + 1).toNat]!) :: computeForwardScores (pos + 1) (scoreAtPos + a[(pos + 1).toNat]!) a

def computeScores (pos : Int) (scoreAtPos : Int) (a : List Int) : List Int :=
  let backwards := computeBackwardScores pos scoreAtPos a
  let forwards := computeForwardScores pos scoreAtPos a
  backwards ++ forwards

def isValidInitialScore (pos : Int) (k : Int) (a : List Int) (b : List Int) : Bool :=
  let scores := computeScores pos b[0]! a
  b.all (fun score => score ∈ scores)

def validInitialScores (k : Int) (a : List Int) (b : List Int) : List Int :=
  (List.range k.toNat).map (Int.ofNat) |>.filter (fun i => isValidInitialScore i k a b) 
    |>.map (fun i => computeInitialScore i a b)

def ValidInput (k : Int) (n : Int) (a : List Int) (b : List Int) : Prop :=
  k > 0 ∧ n > 0 ∧ a.length = k.toNat ∧ b.length = n.toNat ∧ n ≤ k ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < n → b[i.toNat]! ≠ b[j.toNat]!) ∧
  (∀ i, 0 ≤ i ∧ i < k → -2000 ≤ a[i.toNat]! ∧ a[i.toNat]! ≤ 2000) ∧
  (∀ i, 0 ≤ i ∧ i < n → -4000000 ≤ b[i.toNat]! ∧ b[i.toNat]! ≤ 4000000)

@[reducible, simp]
def solve_precond (k n : Int) (a b : List Int) : Prop :=
  ValidInput k n a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (k n : Int) (a b : List Int) (h_precond : solve_precond k n a b) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (k n : Int) (a b : List Int) (result : Int) (h_precond : solve_precond k n a b) : Prop :=
  result ≥ 0 ∧ result ≤ k ∧ result = (validInitialScores k a b).length

theorem solve_spec_satisfied (k n : Int) (a b : List Int) (h_precond : solve_precond k n a b) :
    solve_postcond k n a b (solve k n a b h_precond) h_precond := by
  sorry
-- </vc-theorems>