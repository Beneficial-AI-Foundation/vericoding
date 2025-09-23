-- <vc-preamble>
inductive Bases
| A
| C
| G
| T
deriving Repr, BEq, Inhabited

def Exchanger (s : Array Bases) (x y : Nat) : Array Bases :=
let temp := s[x]!
s.set! x s[y]! |>.set! y temp
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
theorem Exchanger_spec (s : Array Bases) (x y : Nat) :
0 < s.size ∧ x < s.size ∧ y < s.size →
let t := Exchanger s x y
t.size = s.size ∧
(∀ b : Nat, 0 ≤ b ∧ b < s.size ∧ b ≠ x ∧ b ≠ y → t[b]! == s[b]!) ∧
t[x]! == s[y]! ∧ s[x]! == t[y]! :=
sorry
-- </vc-theorems>