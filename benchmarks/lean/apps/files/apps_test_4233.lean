-- <vc-preamble>
-- Helper functions for string operations (axiomatized for this verification)
axiom Split : String → Char → List String
axiom StringToInt : String → Int
noncomputable def IntToString : Int → String := fun _ => ""
axiom AbsInt : Int → Int

-- Safe list access functions
def listGetOr (l : List α) [Inhabited α] (i : Nat) : α :=
  if i < l.length then l[i]! else default

def stringGetOr (s : String) (i : Nat) : Char :=
  if i < s.length then s.data[i]! else ' '

-- Conversion helpers
def intToNat (i : Int) : Nat :=
  if i ≥ 0 then i.natAbs else 0

-- Forward declarations to avoid ordering issues
def CoveredByStar (x y size i j : Int) : Prop :=
  (i = x ∧ j = y) ∨
  (i = x ∧ 1 ≤ AbsInt (j - y) ∧ AbsInt (j - y) ≤ size) ∨
  (j = y ∧ 1 ≤ AbsInt (i - x) ∧ AbsInt (i - x) ≤ size)

def CoveredByStars (stars : List (Int × Int × Int)) (i j : Int) : Prop :=
  ∃ s ∈ stars, CoveredByStar s.1 s.2.1 s.2.2 i j

def ValidStar (n m x y s : Int) : Prop :=
  x ≥ 1 ∧ x ≤ n ∧ y ≥ 1 ∧ y ≤ m ∧ s > 0 ∧
  x - s ≥ 1 ∧ x + s ≤ n ∧ y - s ≥ 1 ∧ y + s ≤ m

-- Recursive helper with termination proof
noncomputable def FormatStarOutputHelper (result : String) (stars : List (Int × Int × Int)) (idx : Nat) : String :=
  if idx ≥ stars.length then result
  else 
    let newResult := result ++ IntToString stars[idx]!.1 ++ " " ++ IntToString stars[idx]!.2.1 ++ " " ++ IntToString stars[idx]!.2.2 ++ "\n"
    FormatStarOutputHelper newResult stars (idx + 1)
termination_by stars.length - idx

def ValidStarDecomposition (input : String) (stars : List (Int × Int × Int)) : Prop :=
  let lines := Split input '\n'
  let firstLine := Split (listGetOr lines 0) ' '
  let n := StringToInt (listGetOr firstLine 0)
  let m := StringToInt (listGetOr firstLine 1)
  (∀ s ∈ stars, 
      s.1 ≥ 1 ∧ s.1 ≤ n ∧ s.2.1 ≥ 1 ∧ s.2.1 ≤ m ∧ s.2.2 > 0 ∧
      ValidStar n m s.1 s.2.1 s.2.2) ∧
  (∀ i j, 1 ≤ i ∧ i ≤ n ∧ 1 ≤ j ∧ j ≤ m →
      let line := listGetOr lines (intToNat i)
      let char := stringGetOr line (intToNat (j - 1))
      (char = '*' ↔ CoveredByStars stars i j) ∧
      (char = '.' ↔ ¬CoveredByStars stars i j))

def ValidInput (input : String) : Prop :=
  let lines := Split input '\n'
  lines.length ≥ 1 ∧ 
  (let firstLine := Split (listGetOr lines 0) ' '
   firstLine.length = 2 ∧
   StringToInt (listGetOr firstLine 0) > 0 ∧ StringToInt (listGetOr firstLine 1) > 0 ∧
   (let n := StringToInt (listGetOr firstLine 0)
    let m := StringToInt (listGetOr firstLine 1)
    n ≥ 3 ∧ m ≥ 3 ∧ lines.length ≥ intToNat n + 1 ∧
    (∀ i, 1 ≤ i ∧ i ≤ n → intToNat i < lines.length ∧ (listGetOr lines (intToNat i)).length ≥ intToNat m) ∧
    (∀ i j, 1 ≤ i ∧ i ≤ n ∧ 0 ≤ j ∧ j < m → 
      let line := listGetOr lines (intToNat i)
      let char := stringGetOr line (intToNat j)
      char = '*' ∨ char = '.')))

def ExistsValidStarDecomposition (input : String) : Prop :=
  let lines := Split input '\n'
  let firstLine := Split (listGetOr lines 0) ' '
  let n := StringToInt (listGetOr firstLine 0)
  let m := StringToInt (listGetOr firstLine 1)
  ∃ k : Int, ∃ stars : List (Int × Int × Int), 
      0 ≤ k ∧ k ≤ n * m ∧ stars.length = intToNat k ∧
      (∀ s ∈ stars, 1 ≤ s.1 ∧ s.1 ≤ n ∧ 1 ≤ s.2.1 ∧ s.2.1 ≤ m ∧ 1 ≤ s.2.2 ∧ s.2.2 ≤ min n m) ∧
      ValidStarDecomposition input stars

def StartsWithIntAndValidFormat (s : String) (k : Int) : Prop :=
  s.length > 0 ∧ 
  (IntToString k).length ≤ s.length ∧ 
  s.take (IntToString k).length = IntToString k

noncomputable def FormatStarOutput (k : Int) (stars : List (Int × Int × Int)) : String :=
  let result := IntToString k ++ "\n"
  FormatStarOutputHelper result stars 0

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  (ValidInput input → 
      (result = "-1\n" ↔ ¬ExistsValidStarDecomposition input)) ∧
  (ValidInput input ∧ result ≠ "-1\n" →
      (∃ k : Int, ∃ stars : List (Int × Int × Int),
          k ≥ 0 ∧ stars.length = intToNat k ∧
          ValidStarDecomposition input stars ∧
          result = FormatStarOutput k stars)) ∧
  (ValidInput input → result ≠ "") ∧
  (¬ValidInput input → result = "-1\n") ∧
  (result = "-1\n" ∨ (∃ k : Int, k ≥ 0 ∧ StartsWithIntAndValidFormat result k)) ∧
  (result = "" ∨ result.drop (result.length - 1) = "\n")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>