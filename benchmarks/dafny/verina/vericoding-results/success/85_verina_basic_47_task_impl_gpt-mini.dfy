// <vc-preamble>
function SumTo(a: seq<int>, n: int): int
    requires 0 <= n <= |a|
    decreases n
{
    if n <= 0 then 0 else SumTo(a, n - 1) + a[n - 1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): lemma for one-step SumTo expansion */
lemma SumTo_step(a: seq<int>, n: int)
  requires 1 <= n <= |a|
  ensures SumTo(a, n) == SumTo(a, n - 1) + a[n - 1]
{
  // Follows directly from the definition of SumTo
  assert SumTo(a, n) == if n <= 0 then 0 else SumTo(a, n - 1) + a[n - 1];
  assert SumTo(a, n) == SumTo(a, n - 1) + a[n - 1];
}

// </vc-helpers>

// <vc-spec>
method ArraySum(a: seq<int>) returns (result: int)
    requires |a| > 0
    ensures result == SumTo(a, |a|)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): loop-based summation without deprecated semicolons */
  var i := 0;
  var acc := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant acc == SumTo(a, i)
  {
    SumTo_step(a, i + 1);
    acc := acc + a[i];
    i := i + 1;
  }
  result := acc;
}

// </vc-code>
