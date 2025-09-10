predicate ValidInput(n: int, k: int)
{
    n >= 1 && k > 0
}

predicate IsCorrectResult(n: int, k: int, result: int)
    requires k > 0
{
    result > n && result % k == 0 && forall x :: n < x < result ==> x % k != 0
}

// <vc-helpers>
lemma DivBounds(n: int, k: int)
  requires k > 0
  ensures n / k * k <= n < (n / k + 1) * k
{
  var q := n / k;
  assert q * k <= n;
  assert n < (q + 1) * k;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures IsCorrectResult(n, k, result)
// </vc-spec>
// <vc-code>
{
  var q := n / k;
  result := (q + 1) * k;
  DivBounds(n, k);
  // result > n
  assert n < result;
  // result is a multiple of k
  assert result % k == 0;
  // minimality: no multiple of k strictly between n and result
  forall x | n < x < result
  {
    if x % k == 0 {
      var m := x / k;
      // x equals m*k because x % k == 0
      assert x == m * k;
      // from x < result = (q+1)*k we get m < q+1
      assert m < q + 1;
      assert m <= q;
      // from q*k <= n and x > n we get m*k > q*k, hence m > q
      assert q * k <= n;
      assert m * k > q * k;
      assert m > q;
      // contradiction: m <= q and m > q
      assert false;
    }
  }
}
// </vc-code>

