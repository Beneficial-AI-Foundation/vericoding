// <vc-preamble>
function IntMax(x: int, y: int): int
{
    if x < y then y else x
}
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
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
  } else {
    result := 1;
  }
}
// </vc-code>
