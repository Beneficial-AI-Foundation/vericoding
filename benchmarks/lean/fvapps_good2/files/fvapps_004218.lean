-- <vc-preamble>
def listMax : List Int → Int
  | [] => 0
  | (x::xs) => max x (listMax xs)

def listMin : List Int → Int
  | [] => 0
  | (x::xs) => min x (listMin xs)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def consecutive (lst : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem consecutive_empty : consecutive [] = 0 :=
sorry

theorem consecutive_property {lst : List Int} (h : lst ≠ []) :
  consecutive lst = listMax lst - listMin lst + 1 - lst.length :=
sorry
-- </vc-theorems>