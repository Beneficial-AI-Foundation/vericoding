-- <vc-preamble>
def List.insertIntoSorted (x : Int) : List Int → List Int 
  | [] => [x]
  | y::ys => if x ≤ y then x::y::ys else y::(insertIntoSorted x ys)

def List.sortList : List Int → List Int 
  | [] => []
  | x::xs => insertIntoSorted x (sortList xs)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shuffled_array (arr : List Int) : List Int := sorry 

theorem shuffled_array_valid_properties {arr : List Int} (h : arr.length ≥ 2) :
  let orig := (arr.take (arr.length - 1)).sortList
  let total := arr.take (arr.length - 1) |>.foldl (· + ·) 0
  let result := shuffled_array (orig ++ [total])
  result.length = orig.length ∧ result.sortList = orig
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem shuffled_array_invalid {arr : List Int} 
  (h : ∀ (i : Nat) (h : i < arr.length), 
    arr.get ⟨i, h⟩ ≠ ((arr.take i ++ arr.drop (i+1)).foldl (· + ·) 0)) :
  shuffled_array arr = [] := sorry

theorem shuffled_array_single {x : Int} :
  shuffled_array [x] = [] := sorry
-- </vc-theorems>