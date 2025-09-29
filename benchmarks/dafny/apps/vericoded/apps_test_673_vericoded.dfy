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

lemma IntStrictLtPlusOneImpliesLe(m: int, q: int)
  ensures m < q + 1 ==> m <= q
{
  if m < q + 1 {
    if !(m <= q) {
      // then m > q, hence m >= q+1 for integers; contradiction
      assert m > q;
      assert m >= q + 1;
      assert !(m < q + 1);
      assert false;
    }
  }
}

lemma MulDivCancel(a: int, k: int)
  requires k > 0
  ensures (a * k) / k == a
{
  var q := (a * k) / k;
  // From DivBounds applied to a*k we get q*k <= a*k < (q+1)*k
  DivBounds(a * k, k);
  // use the inequalities to show q == a
  assert q * k <= a * k;
  assert a * k < (q + 1) * k;
  // if q > a then q*k > a*k, contradicting q*k <= a*k
  if !(q <= a) {
    assert q > a;
    assert q * k > a * k;
    assert false;
  }
  // from a*k < (q+1)*k we have a < q+1, thus a <= q
  assert a < q + 1;
  IntStrictLtPlusOneImpliesLe(a, q);
  assert a <= q;
  // combine to get equality
  assert q == a;
}

lemma ModMulZero(a: int, k: int)
  requires k > 0
  ensures (a * k) % k == 0
{
  MulDivCancel(a, k);
  // remainder formula yields 0
  assert (a * k) % k == 0;
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
  ModMulZero(q + 1, k);
  assert result % k == 0;
  // minimality: no multiple of k strictly between n and result
  forall x | n < x < result ensures x % k != 0
  {
    if x % k == 0 {
      var m := x / k;
      assert x == m * k;
      // from x < result = (q+1)*k we get m < q+1
      assert m < q + 1;
      IntStrictLtPlusOneImpliesLe(m, q);
      assert m <= q;
      // from q*k <= n and x > n we get m*k > q*k
      assert q * k <= n;
      assert m * k > q * k;
      // since k > 0, m > q
      assert m > q;
      // contradiction: m <= q and m > q
      assert false;
    }
  }
}
// </vc-code>

