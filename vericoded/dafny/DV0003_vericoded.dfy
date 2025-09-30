// <vc-preamble>
function IntMax(x: int, y: int): int
{
    if x < y then y else x
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added reads clause to functions */
function LIS(a: array<int>, i: int): int
  requires 0 <= i <= a.Length
  reads a
  decreases i
  ensures LIS(a, i) >= 0
  ensures LIS(a, i) <= i
{
  if i == 0 then
    0
  else
    var prev := LIS(a, i-1);
    var includeCurrent := 1 + LISEndingAt(a, i-1, a[i-1]);
    IntMax(prev, includeCurrent)
}

function LISEndingAt(a: array<int>, i: int, maxVal: int): int
  requires 0 <= i <= a.Length
  reads a
  decreases i
  ensures LISEndingAt(a, i, maxVal) >= 0
  ensures LISEndingAt(a, i, maxVal) <= i
{
  if i == 0 then
    0
  else if a[i-1] < maxVal then
    IntMax(1 + LISEndingAt(a, i-1, a[i-1]), LISEndingAt(a, i-1, maxVal))
  else
    LISEndingAt(a, i-1, maxVal)
}
// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(a: array<int>) returns (result: int)
    ensures result >= 0
    ensures result <= a.Length
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Using LIS function with proper bounds */
  if a.Length == 0 {
    result := 0;
  } else {
    result := LIS(a, a.Length);
  }
}
// </vc-code>
