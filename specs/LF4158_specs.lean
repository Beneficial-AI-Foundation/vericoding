-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_no_duplicates (nums : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_no_duplicates_empty :
  sum_no_duplicates [] = 0 :=
sorry

theorem sum_no_duplicates_singles (nums : List Int) :
  let count := nums.foldl (fun acc n => 
    match acc.find? (fun p => p.1 = n) with
    | none => (n, 1) :: acc
    | some _ => acc.map (fun p => if p.1 = n then (p.1, p.2 + 1) else p)
    ) []
  let singles := count.filter (fun p => p.2 = 1)
  sum_no_duplicates nums = singles.foldl (fun acc p => acc + p.1) 0 :=
sorry 

theorem sum_no_duplicates_none (nums : List Int) :
  let count := nums.foldl (fun acc n => 
    match acc.find? (fun p => p.1 = n) with
    | none => (n, 1) :: acc
    | some _ => acc.map (fun p => if p.1 = n then (p.1, p.2 + 1) else p)
    ) []
  count.filter (fun p => p.2 = 1) = [] →
  sum_no_duplicates nums = 0 :=
sorry

theorem sum_no_duplicates_all_duplicates (nums : List Int) :
  nums.length > 1 →
  sum_no_duplicates (nums ++ nums) = 0 :=
sorry
-- </vc-theorems>