// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int {
  if a > b then a else b
}

function min(a: int, b: int): int {
  if a < b then a else b
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
  if heights.Length < 3 {
    result := 0;
    return;
  }
  var n := heights.Length;
  var left := new int[n];
  var right := new int[n];
  // compute left max
  left[0] := heights[0];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    decreases n - i
  {
    left[i] := if left[i-1] > heights[i] then left[i-1] else heights[i];
    i := i + 1;
  }
  // compute right max
  right[n-1] := heights[n-1];
  var k := n - 2;
  while k >= 0
    invariant -1 <= k < n
    decreases k + 1
  {
    right[k] := if right[k+1] > heights[k] then right[k+1] else heights[k];
    k := k - 1;
  }
  // accumulate trapped water
  result := 0;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result >= 0
    decreases n - i
  {
    var m := if left[i] < right[i] then left[i] else right[i];
    var add := m - heights[i];
    if add > 0 { result := result + add; }
    i := i + 1;
  }
}
// </vc-code>
