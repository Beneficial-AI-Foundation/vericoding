// <vc-preamble>
function SumTo(a: seq<int>, n: int): int
    requires 0 <= n <= |a|
    decreases n
{
    if n <= 0 then 0 else SumTo(a, n - 1) + a[n - 1]
}
// </vc-preamble>

// <vc-helpers>
lemma SumTo_next(a: seq<int>, n: int) requires 0 <= n < |a| ensures SumTo(a, n+1) == SumTo(a, n) + a[n] { }
// </vc-helpers>

// <vc-spec>
method ArraySum(a: seq<int>) returns (result: int)
    requires |a| > 0
    ensures result == SumTo(a, |a|)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var acc := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant acc == SumTo(a, i)
  {
    SumTo_next(a, i);
    acc := acc + a[i];
    i := i + 1;
  }
  result := acc;
}
// </vc-code>
