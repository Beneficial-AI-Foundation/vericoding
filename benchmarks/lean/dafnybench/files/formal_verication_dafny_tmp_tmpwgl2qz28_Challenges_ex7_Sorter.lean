-- <vc-preamble>
inductive Bases
| A
| C
| G
| T

def below (first second : Bases) : Prop :=
first = second ∨
first = Bases.A ∨
(first = Bases.C ∧ (second = Bases.G ∨ second = Bases.T)) ∨
(first = Bases.G ∧ second = Bases.T) ∨
second = Bases.T
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bordered (s : Array Bases) : Bool :=
sorry

def Sorter (bases : Array Bases) : Array Bases :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sorter_spec (bases : Array Bases) :
0 < bases.size →
let sobases := Sorter bases
(sobases.size = bases.size) ∧
bordered sobases :=
sorry
-- </vc-theorems>