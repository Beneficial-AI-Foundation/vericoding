def largest_sum (arr : List Int) : Int := sorry

theorem largest_sum_nonnegative (arr : List Int) :
  largest_sum arr ≥ 0 := sorry

def sum_positives (arr : List Int) : Int := 
  (arr.filter (fun x => x > 0)).foldl (· + ·) 0

-- <vc-helpers>
-- </vc-helpers>

def is_contiguous_subsequence_sum (arr : List Int) (target : Int) : Bool := 
  let n := arr.length
  let indices := List.range n
  indices.any fun i =>
    let subSeqLengths := List.range (n - i)
    subSeqLengths.any fun len =>
      let subseqSum := (List.range len).foldl (fun sum j => 
        match arr.get? (i + j) with
        | none => sum
        | some v => sum + v
      ) 0
      subseqSum = target

/-
info: 0
-/
-- #guard_msgs in
-- #eval largest_sum [-1, -2, -3]

/-
info: 0
-/
-- #guard_msgs in
-- #eval largest_sum []

/-
info: 6
-/
-- #guard_msgs in
-- #eval largest_sum [1, 2, 3]

/-
info: 187
-/
-- #guard_msgs in
-- #eval largest_sum [31, -41, 59, 26, -53, 58, 97, -93, -23, 84]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible