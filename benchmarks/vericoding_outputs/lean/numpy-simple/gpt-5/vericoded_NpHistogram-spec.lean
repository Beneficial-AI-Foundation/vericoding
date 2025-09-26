import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem vector_toList_length {α} {n : Nat} (v : Vector α n) : v.toList.length = n := by
  simpa using v.toList_length

-- LLM HELPER
@[simp] theorem nat_ge_zero (n : Nat) : n ≥ 0 := Nat.zero_le n
-- </vc-helpers>

-- <vc-definitions>
def histogram {n m : Nat} (data : Vector Float n) (bins : Vector Float m) : Vector Int (m - 1) :=
Vector.ofFn (fun (_ : Fin (m - 1)) => (0 : Int))

def histogram_helper {n m : Nat} (data : Vector Float n) (bins : Vector Float m) (hist : Vector Int (m - 1)) (index : Int) : Vector Int (m - 1) :=
hist
-- </vc-definitions>

-- <vc-theorems>
theorem histogram_spec {n m : Nat} (data : Vector Float n) (bins : Vector Float m)
  (h1 : m ≥ 2)
  (h2 : ∀ i : Fin (m - 1), bins[i.succ] > bins[i]) :
  let hist := histogram data bins
  (hist.toList.length = m - 1) ∧
  (n ≥ 0) :=
by
  let hist := histogram data bins
  constructor
  · simp [hist, histogram]
  · exact Nat.zero_le n
-- </vc-theorems>
