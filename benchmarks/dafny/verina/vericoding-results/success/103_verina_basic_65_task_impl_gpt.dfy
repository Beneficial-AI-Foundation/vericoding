// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma SquareGEArg(x: nat)
  ensures x <= x * x
{
  if x == 0 {
  } else {
    assert x - 1 >= 0;
    assert x * (x - 1) >= 0;
    assert x * x - x == x * (x - 1);
    assert x * x - x >= 0;
    assert x <= x * x;
  }
}
// </vc-helpers>

// <vc-spec>
method SquareRoot(n: nat) returns (result: nat)
    ensures result * result <= n
    ensures n < (result + 1) * (result + 1)
// </vc-spec>
// <vc-code>
{
  var k: nat := 0;
  while ((k + 1) * (k + 1) <= n)
    invariant k * k <= n
    invariant k <= n
    decreases n - k
  {
    SquareGEArg(k + 1);
    assert k + 1 <= (k + 1) * (k + 1);
    assert (k + 1) * (k + 1) <= n;
    k := k + 1;
  }
  result := k;
  assert n < (result + 1) * (result + 1);
}
// </vc-code>
