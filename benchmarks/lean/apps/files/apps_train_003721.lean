def List.insertIntoSorted (x : Int) : List Int → List Int 
  | [] => [x]
  | y::ys => if x ≤ y then x::y::ys else y::(insertIntoSorted x ys)

def List.sortList : List Int → List Int 
  | [] => []
  | x::xs => insertIntoSorted x (sortList xs)

-- <vc-helpers>
-- </vc-helpers>

def shuffled_array (arr : List Int) : List Int := sorry 

theorem shuffled_array_valid_properties {arr : List Int} (h : arr.length ≥ 2) :
  let orig := (arr.take (arr.length - 1)).sortList
  let total := arr.take (arr.length - 1) |>.foldl (· + ·) 0
  let result := shuffled_array (orig ++ [total])
  result.length = orig.length ∧ result.sortList = orig
  := sorry

theorem shuffled_array_invalid {arr : List Int} 
  (h : ∀ (i : Nat) (h : i < arr.length), 
    arr.get ⟨i, h⟩ ≠ ((arr.take i ++ arr.drop (i+1)).foldl (· + ·) 0)) :
  shuffled_array arr = [] := sorry

theorem shuffled_array_single {x : Int} :
  shuffled_array [x] = [] := sorry

/-
info: [1, 2, 3, 6]
-/
-- #guard_msgs in
-- #eval shuffled_array [1, 12, 3, 6, 2]

/-
info: [-5, -3, 2, 7]
-/
-- #guard_msgs in
-- #eval shuffled_array [1, -3, -5, 7, 2]

/-
info: [-3]
-/
-- #guard_msgs in
-- #eval shuffled_array [-3, -3]

-- Apps difficulty: introductory
-- Assurance level: unguarded