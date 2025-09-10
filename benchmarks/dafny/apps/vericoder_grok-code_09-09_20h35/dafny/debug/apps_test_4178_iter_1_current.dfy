function maxHeightUpTo(heights: seq<int>, index: int): int
  requires |heights| > 0
  requires -1 <= index < |heights|
{
  if index < 0 then 0
  else if index == 0 then heights[0]
  else if heights[index] > maxHeightUpTo(heights, index - 1) 
    then heights[index]
    else maxHeightUpTo(heights, index - 1)
}

predicate ValidInput(n: int, heights: seq<int>)
{
  n >= 1 && |heights| == n && (forall i :: 0 <= i < |heights| ==> heights[i] >= 1)
}

predicate CanMakeNonDecreasing(heights: seq<int>)
  requires |heights| > 0
{
  forall i :: 0 <= i < |heights| ==> heights[i] >= maxHeightUpTo(heights, i) - 1
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, heights: seq<int>) returns (result: string)
  requires ValidInput(n, heights)
  ensures result == "Yes" <==> CanMakeNonDecreasing(heights)
// </vc-spec>
// <vc-code>
result := "Yes";
if |heights| >= 1 {
    var max_so_far := heights[0];
    for i := 1 to |heights| - 1 {
        var max_up_to_i := Int.Max(max_so_far, heights[i]);
        if heights[i] < max_up_to_i - 1 {
            result := "No";
            break;
        }
        max_so_far := max_up_to_i;
    }
}
// </vc-code>

