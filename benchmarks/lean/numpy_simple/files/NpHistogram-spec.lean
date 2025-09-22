-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def histogram {n m : Nat} (data : Vector Float n) (bins : Vector Float m) : Vector Int (m - 1) :=
sorry

def histogram_helper {n m : Nat} (data : Vector Float n) (bins : Vector Float m) (hist : Vector Int (m - 1)) (index : Int) : Vector Int (m - 1) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem histogram_spec {n m : Nat} (data : Vector Float n) (bins : Vector Float m)
  (h1 : m ≥ 2)
  (h2 : ∀ i : Fin (m - 1), bins[i.succ] > bins[i]) :
  let hist := histogram data bins
  (hist.toList.length = m - 1) ∧
  (n ≥ 0) :=
sorry
-- </vc-theorems>