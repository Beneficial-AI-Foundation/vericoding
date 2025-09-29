function AlternatingSum(n: int): int
    requires n > 0
{
    if n == 1 then -1
    else AlternatingSum(n-1) + (if n % 2 == 0 then n else -n)
}

predicate ValidInput(n: int) {
    n > 0
}

// <vc-helpers>
lemma AlternatingSum_formula(n: int)
  requires n > 0
  ensures AlternatingSum(n) == (if n % 2 == 0 then n / 2 else n / 2 - n)
  decreases n
{
  if n == 1 {
    // AlternatingSum(1) == -1 and 1/2 - 1 == -1
    assert AlternatingSum(1) == -1;
    assert 1 / 2 - 1 == -1;
    assert AlternatingSum(1) == 1 / 2 - 1;
  } else {
    // IH for n-1
    AlternatingSum_formula(n - 1);

    if n % 2 == 0 {
      // n even
      // AlternatingSum(n) = AlternatingSum(n-1) + n
      assert AlternatingSum(n) == AlternatingSum(n - 1) + n;
      // n-1 is odd, so IH gives AlternatingSum(n-1) == (n-1)/2 - (n-1)
      assert AlternatingSum(n - 1) == (n - 1) / 2 - (n - 1);
      // compute AlternatingSum(n)
      assert AlternatingSum(n) == (n - 1) / 2 - (n - 1) + n;
      // simplify: - (n-1) + n == 1
      assert (n - 1) / 2 - (n - 1) + n == (n - 1) / 2 + 1;
      var k := n / 2;
      // n even implies n == 2*k
      assert n == 2 * k;
      // therefore (n-1)/2 == k-1, so (n-1)/2 + 1 == k
      assert (n - 1) / 2 == k - 1;
      assert (n - 1) / 2 + 1 == k;
      assert AlternatingSum(n) == k;
      assert AlternatingSum(n) == n / 2;
    } else {
      // n odd
      // AlternatingSum(n) = AlternatingSum(n-1) - n
      assert AlternatingSum(n) == AlternatingSum(n - 1) - n;
      // n-1 is even, so IH gives AlternatingSum(n-1) == (n-1)/2
      assert AlternatingSum(n - 1) == (n - 1) / 2;
      assert AlternatingSum(n) == (n - 1) / 2 - n;
      var k := n / 2;
      // n odd implies n == 2*k + 1, hence (n-1)/2 == k == n/2
      assert n == 2 * k + 1;
      assert (n - 1) / 2 == k;
      assert (n - 1) / 2 == n / 2;
      assert AlternatingSum(n) == n / 2 - n;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == AlternatingSum(n)
    ensures n % 2 == 0 ==> result == n / 2
    ensures n % 2 != 0 ==> result == n / 2 - n
// </vc-spec>
// <vc-code>
{
  var i := 1;
  result := -1;
  while i < n
    invariant 1 <= i <= n
    invariant result == AlternatingSum(i)
    decreases n - i
  {
    i := i + 1;
    if i % 2 == 0 {
      result := result + i;
    } else {
      result := result - i;
    }
  }
  AlternatingSum_formula(n);
}
// </vc-code>

