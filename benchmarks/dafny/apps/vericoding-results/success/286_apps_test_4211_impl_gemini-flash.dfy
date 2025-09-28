// <vc-preamble>
predicate ValidInput(n: int, b: seq<int>)
{
  n >= 2 && |b| == n - 1 && forall i :: 0 <= i < |b| ==> b[i] >= 0
}

predicate CorrectResult(n: int, b: seq<int>, result: int)
  requires ValidInput(n, b)
{
  if n == 2 then
    result == 2 * b[0]
  else
    result == b[0] + b[n-2] + sum_mins(b, n-2)
}
// </vc-preamble>

// <vc-helpers>
function sum_mins(b: seq<int>, k: int): int
    requires k >= 0
    requires k < |b|
  {
    if k == 0 then
      0
    else
      min(b[k-1], b[k]) + sum_mins(b, k-1)
  }

function min(a: int, b: int): int
  {
    if a < b then a else b
  }
// </vc-helpers>

// <vc-spec>
method solve(n: int, b: seq<int>) returns (result: int)
  requires ValidInput(n, b)
  ensures CorrectResult(n, b, result)
// </vc-spec>
// <vc-code>
{
  if n == 2 {
    result := 2 * b[0];
  } else {
    result := b[0] + b[n - 2] + sum_mins(b, n - 2);
  }
}
// </vc-code>
