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

// <vc-helpers>
function min(a: int, b: int): int
{
  if a <= b then a else b
}

function sum_mins(b: seq<int>, k: int): int
  requires k >= 0
  requires k == 0 || k < |b|
{
  if k == 0 then 0
  else sum_mins(b, k - 1) + min(b[k - 1], b[k])
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
    var s := 0;
    var i := 0;
    while i <= n - 3
      invariant 0 <= i <= n - 2
      invariant s == sum_mins(b, i)
    {
      s := s + min(b[i], b[i+1]);
      i := i + 1;
    }
    result := b[0] + b[n-2] + s;
  }
}
// </vc-code>

