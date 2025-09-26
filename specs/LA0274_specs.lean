-- <vc-preamble>
-- String splitting utility (axiomatized for now)
axiom SplitLines : String → List String

@[reducible, simp]
def ValidPokemonName (name : String) : Prop :=
  name = "vaporeon" ∨ name = "jolteon" ∨ name = "flareon" ∨ name = "espeon" ∨
  name = "umbreon" ∨ name = "leafeon" ∨ name = "glaceon" ∨ name = "sylveon"

@[reducible, simp]
def MatchesPattern (pokemonName pattern : String) : Prop :=
  pokemonName.length = pattern.length ∧
  ∀ i, i < pattern.length → (pattern.data[i]! = '.' ∨ pattern.data[i]! = pokemonName.data[i]!)

@[reducible, simp]
def GetPokemonList : List String :=
  ["vaporeon", "jolteon", "flareon", "espeon", "umbreon", "leafeon", "glaceon", "sylveon"]

@[reducible, simp]
def ValidInput (input : String) : Prop :=
  input.length > 0 ∧
  let lines := SplitLines input
  lines.length ≥ 2 ∧
  (lines[0]!).length > 0 ∧ 
  (∀ i, i < (lines[0]!).length → '0' ≤ (lines[0]!).data[i]! ∧ (lines[0]!).data[i]! ≤ '9') ∧
  6 ≤ (lines[1]!).length ∧ (lines[1]!).length ≤ 8 ∧
  (∀ i, i < (lines[1]!).length → (('a' ≤ (lines[1]!).data[i]! ∧ (lines[1]!).data[i]! ≤ 'z') ∨ (lines[1]!).data[i]! = '.')) ∧
  ∃ j, j < GetPokemonList.length ∧ (GetPokemonList[j]!).length = (lines[1]!).length ∧ MatchesPattern (GetPokemonList[j]!) (lines[1]!)

@[reducible, simp]
def IsFirstMatch (result pattern : String) (pokemonList : List String) : Prop :=
  ∃ i, i < pokemonList.length ∧
    (pokemonList[i]!) = result ∧
    result.length = pattern.length ∧
    MatchesPattern result pattern ∧
    ∀ j, j < i → ((pokemonList[j]!).length ≠ pattern.length ∨ ¬MatchesPattern (pokemonList[j]!) pattern)

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
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
  ValidPokemonName result ∧
  (let lines := SplitLines input
   IsFirstMatch result (lines[1]!) GetPokemonList) ∧
  (let lines := SplitLines input
   ∃ i, i < GetPokemonList.length ∧
       (GetPokemonList[i]!) = result ∧
       result.length = (lines[1]!).length ∧
       MatchesPattern result (lines[1]!))

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>