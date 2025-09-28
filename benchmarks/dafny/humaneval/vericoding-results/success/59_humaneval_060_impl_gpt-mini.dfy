// <vc-preamble>

predicate ValidInput(n: int)
{
    n >= 1
}

function SumFromOneToN(n: int): int
    requires n >= 1
{
    n * (n + 1) / 2
}
// </vc-preamble>

// <vc-helpers>
lemma SumStep(k: int)
    requires k >= 1
    ensures (k - 1) * k / 2 + k == k * (k + 1) / 2
  {
    assert (k - 1) * k / 2 + k == ((k - 1) * k + 2 * k) / 2;
    assert (k - 1) * k + 2 * k == k * (k + 1);
    assert ((k - 1) * k + 2 * k) / 2 == k * (k + 1) / 2;
  }
// </vc-helpers>

// <vc-spec>
method sum_to_n(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == SumFromOneToN(n)
// </vc-spec>
// <vc-code>
{
  var i := 1;
  result := 0;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant result == (i - 1) * i / 2
    decreases n - i + 1
  {
    SumStep(i);
    result := result + i;
    i := i + 1;
  }
}
// </vc-code>
