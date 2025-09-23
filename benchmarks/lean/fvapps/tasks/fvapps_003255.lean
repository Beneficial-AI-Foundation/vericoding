-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_uniq (arr : List Float) : Float := sorry

theorem find_uniq_returns_unique (numbers : List Float) (unique_num : Float) (base_num : Float)
    (h1 : numbers.length ≥ 3)
    (h2 : base_num ≠ unique_num)
    (arr := List.replicate (numbers.length + 1) base_num)
    (h3 : ∀ (i : Fin arr.length), (
      if i.val = numbers.length/2 
      then arr.get i = unique_num
      else arr.get i = base_num)) :
    find_uniq arr = unique_num := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_uniq_basic (common unique : Float)
    (h : common ≠ unique) :
    find_uniq [common, common, unique, common, common] = unique := sorry
-- </vc-theorems>