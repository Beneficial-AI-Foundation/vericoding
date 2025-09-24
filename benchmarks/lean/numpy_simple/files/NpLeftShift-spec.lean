-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shiftLeftInt (x : Int) (shift : Nat) : Int :=
sorry

def leftShift {n : Nat} (a : Vector Int n) (b : Vector Nat n)
    (h : ∀ i : Fin n, b[i] < 64) : Vector Int n :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem leftShift_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n)
    (h : ∀ i : Fin n, b[i] < 64) :
  (leftShift a b h).toList.length = n ∧
  ∀ i : Fin n, (leftShift a b h)[i] = shiftLeftInt (a[i]) (b[i]) :=
sorry
-- </vc-theorems>