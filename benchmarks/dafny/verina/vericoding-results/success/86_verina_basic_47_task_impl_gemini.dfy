// <vc-preamble>
function SumTo(a: seq<int>, n: int): int
    requires 0 <= n <= |a|
    decreases n
{
    if n <= 0 then 0 else SumTo(a, n - 1) + a[n - 1]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ArraySum(a: seq<int>) returns (result: int)
    requires |a| > 0
    ensures result == SumTo(a, |a|)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant result == SumTo(a, i)
  {
    result := result + a[i];
    i := i + 1;
  }
}
// </vc-code>
