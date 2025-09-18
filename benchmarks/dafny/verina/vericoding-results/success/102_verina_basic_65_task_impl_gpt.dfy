// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma SquareStrictlyIncreases(i: nat)
  ensures (i + 1) * (i + 1) > i * i
{
  assert (i + 1) * (i + 1) == i * i + 2 * i + 1;
  assert i * i + 2 * i + 1 > i * i;
}
// </vc-helpers>

// <vc-spec>
method SquareRoot(n: nat) returns (result: nat)
    ensures result * result <= n
    ensures n < (result + 1) * (result + 1)
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  while ((i + 1) * (i + 1) <= n)
    invariant i * i <= n
    decreases n - i * i
  {
    var j: nat := i + 1;
    assert j * j <= n;
    assert j * j == i * i + 2 * i + 1;
    assert j * j > i * i;
    i := j;
  }
  result := i;
}
// </vc-code>
