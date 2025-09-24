-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_power (x : Int) : Int :=
  sorry

def getKth (lo hi k : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_power_always_terminates (x : Int)
  (h : x ≥ 1) :
  get_power x ≥ 0 :=
sorry

theorem getKth_input_validation (lo hi k : Int)
  (h1 : lo ≥ 1)
  (h2 : hi ≥ 1)
  (h3 : lo ≤ hi)
  (h4 : k ≥ 1)
  (h5 : k ≤ hi - lo + 1) :
  lo ≤ getKth lo hi k ∧ getKth lo hi k ≤ hi :=
sorry

theorem getKth_sorting_property (lo hi : Int)
  (h1 : lo ≥ 1)
  (h2 : hi ≥ 1)
  (h3 : lo ≤ hi)
  (k1 k2 : Int)
  (h4 : k1 ≥ 1)
  (h5 : k2 ≥ 1)
  (h6 : k1 ≤ hi - lo + 1)
  (h7 : k2 ≤ hi - lo + 1)
  (h8 : k1 < k2) :
  get_power (getKth lo hi k1) < get_power (getKth lo hi k2) ∨
  (get_power (getKth lo hi k1) = get_power (getKth lo hi k2) ∧
   getKth lo hi k1 ≤ getKth lo hi k2) :=
sorry

theorem getKth_single_element (x : Int)
  (h : x ≥ 1) :
  getKth x x 1 = x :=
sorry
-- </vc-theorems>