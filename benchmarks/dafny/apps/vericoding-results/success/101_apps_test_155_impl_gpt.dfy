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
lemma DivLessThanBound(x: int, y: int, z: int)
  requires 0 <= x
  requires 1 <= y
  requires 0 < z
  requires x < y * z
  ensures x / y < z
{
  var q := x / y;
  var r := x % y;
  assert x == y * q + r;
  assert 0 <= r < y;
  assert y * q <= x;
  assert y * q < y * z;
  if q >= z {
    assert y * q >= y * z;
    assert false;
  }
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
    assert |result| == 2;
    assert 1 <= result[0] <= n;
    assert 1 <= result[1] <= m;
  } else {
    var kR := k - n;
    var d := m - 1;
    assert d >= 1;
    assert 0 <= kR;
    assert k < n * m;
    assert kR < n * d;

    var q := kR / d;
    assert q == kR / d;
    DivLessThanBound(kR, d, n);
    assert q < n;
    assert q >= 0;

    var r := n - q;
    assert r <= n;
    assert r >= 1;

    if r % 2 == 1 {
      var c := m - kR % d;
      assert 0 <= kR % d < d;
      assert 2 <= c <= m;
      result := [r, c];
    } else {
      var c := 2 + kR % d;
      assert 0 <= kR % d < d;
      assert 2 <= c <= m;
      result := [r, c];
    }

    assert |result| == 2;
    assert 1 <= result[0] <= n;
    assert 1 <= result[1] <= m;
  }
}
// </vc-code>

