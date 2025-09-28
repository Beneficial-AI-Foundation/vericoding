// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function leftMax(heights: array<int>, idx: int): int
  requires 0 <= idx < heights.Length
  decreases idx
  reads heights
{
  if idx == 0 then heights[0] else (if leftMax(heights, idx - 1) > heights[idx] then leftMax(heights, idx - 1) else heights[idx])
}

function rightMax(heights: array<int>, idx: int): int
  requires 0 <= idx < heights.Length
  decreases heights.Length - idx
  reads heights
{
  if idx == heights.Length - 1 then heights[idx] else (if rightMax(heights, idx + 1) > heights[idx] then rightMax(heights, idx + 1) else heights[idx])
}

function waterAt(heights: array<int>, idx: int): int
  requires 0 <= idx < heights.Length
  requires heights.Length >= 3
  reads heights
{
  var l := leftMax(heights, idx);
  var r := rightMax(heights, idx);
  (if l < r then l else r) - heights[idx]
}
// </vc-helpers>

// <vc-spec>
method Rain(heights: array<int>) returns (result: int)
    requires forall i :: 0 <= i < heights.Length ==> heights[i] >= 0
    ensures result >= 0
    ensures heights.Length < 3 ==> result == 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed termination errors by adding decreases clauses to recursive functions */
  if heights.Length < 3 {
    result := 0;
  } else {
    var total := 0;
    var i := 0;
    while i < heights.Length
      invariant 0 <= i <= heights.Length
      invariant total >= 0
    {
      total := total + waterAt(heights, i);
      i := i + 1;
    }
    result := total;
  }
}
// </vc-code>
