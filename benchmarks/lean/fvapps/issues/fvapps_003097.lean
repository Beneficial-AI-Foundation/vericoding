-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def transpose (amount : Int) (tab : List String) : List String := sorry

def Nat.toString (n : Nat) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem transpose_basic_format 
  (tab : List String)
  (amount : Int)
  (h1 : -5 ≤ amount)
  (h2 : amount ≤ 5) :
  let result := transpose amount tab
  if result ≠ ["Out of frets!"] then
    (∀ r ∈ result, 
      r.length > 0 ∧ 
      ((r.data.get? 0).isSome ∧
       ((r.data.get? 0).getD '_' = 'e' ∨ 
        (r.data.get? 0).getD '_' = 'E' ∨
        (r.data.get? 0).getD '_' = 'B' ∨
        (r.data.get? 0).getD '_' = 'G' ∨
        (r.data.get? 0).getD '_' = 'D' ∨
        (r.data.get? 0).getD '_' = 'A')) ∧
      (r.data.get? 1).isSome ∧
      (r.data.get? 1).getD '_' = '|') ∧
    result.length = 6 ∧
    (∀ line ∈ result,
      ∀ n : Nat,
      (n ≥ 0 ∧ n ≤ 22))
  else True :=
sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval transpose 2 ["e|-------5-7-----7-|-8-----8-2-----2-|-0---------0-----|-----------------|", "B|-----5-----5-----|---5-------3-----|---1---1-----1---|-0-1-1-----------|", "G|---5---------5---|-----5-------2---|-----2---------2-|-0-2-2-----------|", "D|-7-------6-------|-5-------4-------|-3---------------|-----------------|", "A|-----------------|-----------------|-----------------|-2-0-0---0--/8-7-|", "E|-----------------|-----------------|-----------------|-----------------|"]

/-
info: 'Out of frets!'
-/
-- #guard_msgs in
-- #eval transpose -1 ["e|-----------------|---------------|----------------|------------------|", "B|-----------------|---------------|----------------|------------------|", "G|--0---3---5----0-|---3---6-5-----|-0---3---5----3-|---0----(0)-------|", "D|--0---3---5----0-|---3---6-5-----|-0---3---5----3-|---0----(0)-------|", "A|-----------------|---------------|----------------|------------------|", "E|-----------------|---------------|----------------|------------------|"]
-- </vc-theorems>