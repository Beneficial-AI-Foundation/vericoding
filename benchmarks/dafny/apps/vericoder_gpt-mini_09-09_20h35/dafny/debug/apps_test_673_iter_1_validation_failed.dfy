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
lemma NextMultipleIsCorrect(n: int, k: int)
  requires n >= 1 && k > 0
  ensures IsCorrectResult(n, k, (n / k + 1) * k)
{
  var q := n / k;
  var r := n % k;
  assert n == q * k + r;
  assert 0 <= r && r < k;

  var result := (q + 1) * k;

  // result > n
  assert result - n == k - r;
  assert k - r > 0;
  assert result > n;

  // result is multiple of k
  assert result % k == 0;

  // no multiple of k strictly between n and result
  assert forall x :: n < x < result ==> x % k != 0
  proof {
    var x: int;
    assume H: n < x < result;
    assume M: x % k == 0;

    var t := x / k;
    assert x == t * k;

    // From n == q*k + r and 0 <= r we have q*k <= n < x, so q*k < x
    assert q * k <= n;
    assert n < x;
    assert q * k < x;

    // x == t*k so q*k < t*k, and since k > 0, q < t
    assert q * k < t * k;
    assert q < t;

    // From x < result = (q+1)*k we get t*k < (q+1)*k and hence t < q+1
    assert t * k < (q + 1) * k;
    assert t < q + 1;

    // Contradiction: integer t cannot satisfy q < t < q+1
    assert false;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures IsCorrectResult(n, k, result)
// </vc-spec>
// <vc-code>
{
  result := (n / k + 1) * k;
  NextMultipleIsCorrect(n, k);
}
// </vc-code>

