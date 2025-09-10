predicate ValidResult(n: int, result: int)
  requires n >= 0
{
  var quotient := n / 10;
  var remainder := n % 10;
  result % 10 == 0 && 
  result >= 0 &&
  (remainder < 5 ==> result == quotient * 10) &&
  (remainder > 5 ==> result == (quotient + 1) * 10) &&
  (remainder == 5 ==> (quotient % 2 == 0 ==> result == quotient * 10) && 
                      (quotient % 2 == 1 ==> result == (quotient + 1) * 10))
}

// <vc-helpers>
lemma RoundingLemma(n: int, q: int, r: int)
  requires n >= 0
  requires q == n / 10
  requires r == n % 10
  ensures (r < 5 ==> q * 10 == (n + 4) / 10 * 10) &&
          (r > 5 ==> (q + 1) * 10 == (n + 4) / 10 * 10) &&
          (r == 5 ==> (q % 2 == 0 ==> q * 10 == (n + 4) / 10 * 10) && 
                      (q % 2 == 1 ==> (q + 1) * 10 == (n + 4) / 10 * 10))
{
  if r < 5 {
    assert n == 10 * q + r && r < 5;
    assert n + 4 == 10 * q + (r + 4);
    assert r + 4 < 9;
    assert (n + 4) / 10 == q;
    assert q * 10 == (n + 4) / 10 * 10;
  } else if r > 5 {
    assert n == 10 * q + r && r > 5;
    assert n + 4 == 10 * q + (r + 4);
    assert r >= 6 && r <= 9;
    assert r + 4 >= 10;
    assert (n + 4) / 10 == q + 1;
    assert (q + 1) * 10 == (n + 4) / 10 * 10;
  } else if r == 5 {
    if q % 2 == 0 {
      assert n == 10 * q + 5;
      assert n + 4 == 10 * q + 9;
      assert (n + 4) / 10 == q;
      assert q * 10 == (n + 4) / 10 * 10;
    } else {
      assert n == 10 * q + 5;
      assert n + 4 == 10 * q + 9;
      assert q % 2 == 1;
      assert (n + 4) / 10 == q;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires n >= 0
  ensures ValidResult(n, result)
// </vc-spec>
// <vc-code>
{
  var q := n / 10;
  var r := n % 10;
  if r < 5 {
    result := q * 10;
  } else if r > 5 {
    result := (q + 1) * 10;
  } else {
    if q % 2 == 0 {
      result := q * 10;
    } else {
      result := (q + 1) * 10;
    }
  }
  assert ValidResult(n, result) by {
    RoundingLemma(n, q, r);
  }
}
// </vc-code>

