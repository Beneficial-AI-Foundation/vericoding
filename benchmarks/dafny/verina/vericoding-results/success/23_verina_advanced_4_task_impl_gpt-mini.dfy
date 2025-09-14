// <vc-preamble>
function IntMax(x: int, y: int): int
{
    if x < y then y else x
}
// </vc-preamble>

// <vc-helpers>
function Min(a: int, b: int): int { if a < b then a else b }
predicate NonNegative(x: int) { x >= 0 }
// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(a: array<int>) returns (result: int)
    ensures result >= 0
    ensures result <= a.Length
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  if n == 0 {
    result := 0;
    return;
  }
  var lis := new int[n];
  result := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result >= 0 && result <= n
    invariant forall k | 0 <= k < i :: lis[k] >= 1 && lis[k] <= k + 1
    decreases n - i
  {
    lis[i] := 1;
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant lis[i] >= 1 && lis[i] <= i + 1
      invariant forall k | 0 <= k < i :: lis[k] >= 1 && lis[k] <= k + 1
      decreases i - j
    {
      if a[j] < a[i] {
        var cand := lis[j] + 1;
        if cand > lis[i] {
          lis[i] := cand;
        }
      }
      j := j + 1;
    }
    if lis[i] > result {
      result := lis[i];
    }
    i := i + 1;
  }
}

// </vc-code>
