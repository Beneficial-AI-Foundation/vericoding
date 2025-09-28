// <vc-preamble>
function SumTo(a: seq<int>, n: int): int
    requires 0 <= n <= |a|
    decreases n
{
    if n <= 0 then 0 else SumTo(a, n - 1) + a[n - 1]
}
// </vc-preamble>

// <vc-helpers>
lemma LemmaSumToStep(a: seq<int>, i: nat)
  requires i < |a|
  ensures SumTo(a, i + 1) == SumTo(a, i) + a[i]
{
}

// </vc-helpers>

// <vc-spec>
method ArraySum(a: seq<int>) returns (result: int)
    requires |a| > 0
    ensures result == SumTo(a, |a|)
// </vc-spec>
// <vc-code>
{
  var sum: int := 0;
  var i: nat := 0;
  while i < |a|
    invariant i <= |a|
    invariant sum == SumTo(a, i)
    decreases |a| - i
  {
    var j: nat := i;
    LemmaSumToStep(a, j);
    sum := sum + a[j];
    i := j + 1;
  }
  result := sum;
}
// </vc-code>
