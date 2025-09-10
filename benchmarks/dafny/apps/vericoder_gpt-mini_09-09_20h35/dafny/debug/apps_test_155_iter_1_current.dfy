predicate ValidInput(n: int, m: int, k: int) {
    n >= 2 && m >= 2 && n % 2 == 0 && k >= 0 && k < n * m
}

predicate ValidOutput(result: seq<int>, n: int, m: int) {
    |result| == 2 && result[0] >= 1 && result[0] <= n && result[1] >= 1 && result[1] <= m
}

predicate CorrectPosition(result: seq<int>, n: int, m: int, k: int) 
    requires ValidInput(n, m, k)
    requires |result| == 2
{
    if k < n then
        result[0] == k + 1 && result[1] == 1
    else
        var k_remaining := k - n;
        var r := n - k_remaining / (m - 1);
        result[0] == r &&
        (r % 2 == 1 ==> result[1] == m - k_remaining % (m - 1)) &&
        (r % 2 == 0 ==> result[1] == 2 + k_remaining % (m - 1))
}

// <vc-helpers>
lemma DivModBounds(k:int, d:int, n:int)
    requires d > 0 && k >= 0 && k < n * d
    ensures 0 <= k / d <= n - 1
    ensures 0 <= k % d < d
{
    var q := k / d;
    var r := k % d;
    assert k == q * d + r;
    assert 0 <= r;
    assert r < d;
    if q >= n {
        // from k == q*d + r and r >= 0 we get k >= q*d
        assert k >= q * d;
        // hence k >= n*d, contradicting k < n*d
        assert k >= n * d;
        assert false;
    }
    assert q <= n - 1;
    assert 0 <= q;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, m, k)
    ensures ValidOutput(result, n, m)
    ensures CorrectPosition(result, n, m, k)
// </vc-spec>
// <vc-code>
{
  if k < n {
    result := [k + 1, 1];
    return;
  }

  var k_remaining := k - n;
  // k_remaining in [0, n*(m-1) - 1]
  DivModBounds(k_remaining, m - 1, n);
  var rows_from_end := k_remaining / (m - 1);
  var r := n - rows_from_end;
  assert 1 <= r && r <= n;

  var pos := k_remaining % (m - 1);
  var c := if r % 2 == 1 then m - pos else 2 + pos;
  assert 1 <= c && c <= m;

  result := [r, c];
}
// </vc-code>

