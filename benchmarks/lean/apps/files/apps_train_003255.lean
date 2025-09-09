-- <vc-helpers>
-- </vc-helpers>

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

theorem find_uniq_basic (common unique : Float)
    (h : common ≠ unique) :
    find_uniq [common, common, unique, common, common] = unique := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_uniq [1, 1, 1, 2, 1, 1]

/-
info: 0.55
-/
-- #guard_msgs in
-- #eval find_uniq [0, 0, 0.55, 0, 0]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_uniq [4, 4, 4, 3, 4, 4, 4, 4]

-- Apps difficulty: introductory
-- Assurance level: unguarded