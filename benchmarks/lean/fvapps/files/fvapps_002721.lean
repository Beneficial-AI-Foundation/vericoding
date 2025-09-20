-- <vc-preamble>
def sum_positives (arr : List Int) : Int :=
  (arr.filter (fun x => x > 0)).foldl (· + ·) 0

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
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def largest_sum (arr : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem largest_sum_nonnegative (arr : List Int) :
  largest_sum arr ≥ 0 :=
sorry
-- </vc-theorems>