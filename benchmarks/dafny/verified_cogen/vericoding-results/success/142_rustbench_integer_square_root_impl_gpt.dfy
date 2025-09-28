// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma SquareNonNegative(x: int)
  ensures 0 <= x * x
{ }

lemma SquareGEArgWhenArgAtLeastOne(s: int)
  requires s >= 1
  ensures s <= s * s
{ }
// </vc-helpers>

// <vc-spec>
method IntegerSquareRoot(n: int) returns (result: int)
    requires n >= 1
    ensures 0 <= result * result
    ensures result * result <= n
    ensures n < (result + 1) * (result + 1)
// </vc-spec>
// <vc-code>
{
  var r := 0;
  while ((r + 1) * (r + 1) <= n)
    invariant 0 <= r
    invariant r * r <= n
    invariant r <= n
    decreases n - r
  {
    assert r + 1 >= 1;
    SquareGEArgWhenArgAtLeastOne(r + 1);
    assert r + 1 <= n;
    r := r + 1;
  }
  result := r;
  SquareNonNegative(result);
}
// </vc-code>
