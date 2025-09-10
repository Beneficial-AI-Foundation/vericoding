predicate ValidInput(n: int, heights: seq<int>)
{
    n > 0 && |heights| == n &&
    (forall i :: 0 <= i < n ==> heights[i] >= 0) &&
    (forall i :: 0 <= i < n-1 ==> heights[i] < heights[i+1])
}

predicate ValidOutput(n: int, result: seq<int>)
{
    |result| == n &&
    (forall i :: 0 <= i < n ==> result[i] >= 0) &&
    (forall i :: 0 <= i < n-1 ==> result[i] <= result[i+1]) &&
    (forall i :: 0 <= i < n-1 ==> result[i+1] - result[i] <= 1)
}

predicate IsStable(result: seq<int>)
{
    forall i :: 0 <= i < |result|-1 ==> !(result[i] + 2 <= result[i+1])
}

function sum_seq(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum_seq(s[1..])
}

// <vc-helpers>
function StableSort(n: int, heights: seq<int>): (result: seq<int>)
  requires ValidInput(n, heights)
  ensures ValidOutput(n, result)
  ensures sum_seq(result) == sum_seq(heights)
  ensures IsStable(result)
{
  if n == 1 then
    return heights
  else
    var m := n / 2;
    var left := heights[0..m];
    var right := heights[m..n];

    var sortedLeft := StableSort(m, left);
    var sortedRight := StableSort(n - m, right);

    var merged := new int[n];
    var i := 0;
    var j := 0;
    var k := 0;
    while k < n
      invariant 0 <= i <= m
      invariant 0 <= j <= n - m
      invariant 0 <= k < n
      invariant |merged| == n
      invariant forall idx :: 0 <= idx < k ==> merged[idx] >= 0
      invariant forall idx :: 0 <= idx < k - 1 ==> merged[idx] <= merged[idx+1]
      invariant forall idx :: 0 <= idx < k - 1 ==> merged[idx+1] - merged[idx] <= 1
      invariant sum_seq(merged[0..k]) + sum_seq(sortedLeft[i..m]) + sum_seq(sortedRight[j..n-m]) == sum_seq(sortedLeft) + sum_seq(sortedRight)
      invariant (forall x :: m <= x < n ==> sortedRight[x-m] == right[x-m])
      invariant (forall x :: 0 <= x < m ==> sortedLeft[x] == left[x])
    {
      if i < m && (j == n - m || sortedLeft[i] <= sortedRight[j])
      {
        merged[k] := sortedLeft[i];
        i := i + 1;
      }
      else
      {
        merged[k] := sortedRight[j];
        j := j + 1;
      }
      k := k + 1;
    }
    return merged;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, heights: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, heights)
    ensures ValidOutput(n, result)
    ensures sum_seq(result) == sum_seq(heights)
    ensures IsStable(result)
// </vc-spec>
// <vc-code>
{
  result := StableSort(n, heights);
  return result;
}
// </vc-code>

