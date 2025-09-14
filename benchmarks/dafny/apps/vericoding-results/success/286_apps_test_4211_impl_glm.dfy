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
function sum(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + sum(s[1..])
}

function sum_mins(b: seq<int>, k: int): int
  requires 0 <= k <= |b|
{
  if k == 0 then 0
  else (k+1)*b[0] + sum(b[1..k])
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
    result := b[0] + b[n-2] + sum_mins(b, n-2);
  }
}
// </vc-code>

