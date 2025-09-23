-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def next_item {α} [BEq α] (xs : List α) (item : α) : Option α := sorry

theorem next_item_integers {xs : List Int} {x : Int} 
  (h1 : x ∈ xs) (h2 : x ≠ xs[xs.length - 1]!) 
  (h3 : List.indexOf x xs + 1 < xs.length) :
  next_item xs x = some (xs[List.indexOf x xs + 1]!) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem next_item_last {α} [BEq α] [Inhabited α] {xs : List α} {x : α} 
  (h : x = xs[xs.length - 1]!) :
  next_item xs x = none := sorry

theorem next_item_not_found {α} [BEq α] {xs : List α} {x : α} 
  (h : x ∉ xs) :
  next_item xs x = none := sorry

theorem next_item_chars {s : String} {c : Char} 
  (h1 : c ∈ s.toList) (h2 : c ≠ s.toList[s.toList.length - 1]!)
  (h3 : List.indexOf c s.toList + 1 < s.toList.length) :
  next_item s.toList c = some (s.toList[List.indexOf c s.toList + 1]!) := sorry

theorem next_item_sequential {xs : List Int} (h : xs.length ≥ 2) :
  ∀ i, i < xs.length - 1 → 
    (xs[i]! ∉ List.take i xs → next_item xs xs[i]! = some xs[i+1]!) := sorry

theorem next_item_sequential_last {xs : List Int} 
  (h1 : xs.length ≥ 2) 
  (h2 : xs[xs.length - 1]! ∉ List.take (xs.length - 1) xs) :
  next_item xs xs[xs.length - 1]! = none := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval next_item [1, 2, 3, 4, 5] 3

/-
info: 'l'
-/
-- #guard_msgs in
-- #eval next_item "hello" "l"

/-
info: None
-/
-- #guard_msgs in
-- #eval next_item ["a", "b", "c"] "c"
-- </vc-theorems>