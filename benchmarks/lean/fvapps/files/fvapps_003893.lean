-- <vc-preamble>
def numDigits (n : Nat) : Nat :=
  if n < 10 then 1
  else 1 + numDigits (n / 10)

def listSum : List Nat → Nat
  | [] => 0
  | (h::t) => h + listSum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumDig_nthTerm (initVal : Nat) (patternL : List Nat) (nthTerm : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sumDig_nthTerm_bounds {initVal : Nat} {patternL : List Nat} {nthTerm : Nat}
  (h1 : initVal ≤ 50)
  (h2 : ∀ x ∈ patternL, x ≤ 5)
  (h3 : 1 ≤ patternL.length)
  (h4 : patternL.length ≤ 3)
  (h5 : 2 ≤ nthTerm)
  (h6 : nthTerm ≤ 10) :
  0 ≤ sumDig_nthTerm initVal patternL nthTerm ∧
  sumDig_nthTerm initVal patternL nthTerm ≤ 9 * numDigits (initVal + (listSum patternL * nthTerm)) :=
sorry

theorem sumDig_nthTerm_deterministic {initVal : Nat} {patternL : List Nat} {nthTerm : Nat} :
  sumDig_nthTerm initVal patternL nthTerm = sumDig_nthTerm initVal patternL nthTerm :=
sorry
-- </vc-theorems>