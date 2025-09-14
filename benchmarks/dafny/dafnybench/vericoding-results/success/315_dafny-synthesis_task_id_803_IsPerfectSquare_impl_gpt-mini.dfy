

// <vc-helpers>
lemma SquareLessImpliesLess(i: int, n: int)
  requires 0 <= i && 0 <= n && i * i < n
  ensures i < n
{
  if n == 0 {
    // i*i < 0 contradicts 0 <= i
    assert 0 <= i;
    assert 0 <= i * i;
    assert i * i < 0;
    assert false;
  } else {
    // now n >= 1
    if i >= n {
      // i*i - n*n = (i-n)*(i+n) and both factors non-negative, so i*i >= n*n
      assert i * i - n * n == (i - n) * (i + n);
      assert i - n >= 0;
      assert i + n >= 0;
      assert (i - n) * (i + n) >= 0;
      assert i * i - n * n >= 0;
      assert i * i >= n * n;

      // n*n >= n because n*(n-1) >= 0 when n >= 1
      assert n * n - n == n * (n - 1);
      assert n - 1 >= 0;
      assert n * (n - 1) >= 0;
      assert n * n >= n;

      // hence i*i >= n, contradicting i*i < n
      assert i * i >= n;
      assert false;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method IsPerfectSquare(n: int) returns (result: bool)
    requires n >= 0
    ensures result == true ==> (exists i: int :: 0 <= i <= n && i * i == n)
    ensures result == false ==> (forall a: int :: 0 < a*a < n ==> a*a != n)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i * i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    SquareLessImpliesLess(i, n);
    i := i + 1;
  }
  result := i * i == n;
}
// </vc-code>

