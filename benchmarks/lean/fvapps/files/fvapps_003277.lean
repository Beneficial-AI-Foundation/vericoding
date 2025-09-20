-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def snail (column : Int) (day : Int) (night : Int) : Int :=
  sorry

def ceilDiv (a b : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem snail_result_positive {column day night : Int}
  (h1 : column > 0)
  (h2 : day > night)
  (h3 : day > 0)
  (h4 : night ≥ 0) :
  snail column day night ≥ 1 :=
sorry

theorem snail_reaches_top {column day night : Int}
  (h1 : column > 0)
  (h2 : day > night)
  (h3 : day > 0)
  (h4 : night ≥ 0) :
  let result := snail column day night
  (result * day) - ((result-1) * night) ≥ column :=
sorry
-- </vc-theorems>