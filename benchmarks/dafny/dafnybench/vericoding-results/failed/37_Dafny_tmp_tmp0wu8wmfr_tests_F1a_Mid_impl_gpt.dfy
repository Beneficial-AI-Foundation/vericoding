

// <vc-helpers>
set-options "--allow-warnings"

lemma Div2Facts(n:int)
  ensures n == 2 * (n / 2) + n % 2
  ensures 0 <= n % 2 < 2
  ensures 0 <= n ==> 0 <= n / 2
{
  assert n == 2 * (n / 2) + n % 2;
  assert 0 <= n % 2 < 2;
  if 0 <= n {
    assert 0 <= n / 2;
  }
}
// </vc-helpers>

// <vc-spec>
method Mid( p: int, q: int) returns ( m: int )
    // | ... | ??? | ... |
    //        p m   q
    requires p <= q;
    ensures p<= m <= q;
    ensures m-p <= q-m;
    ensures 0 <= (q-m)-(m-p) <= 1;
// </vc-spec>
// <vc-code>
{
  assert 0 <= q - p;
  Div2Facts(q - p);

  var d := (q - p) / 2;
  m := p + d;

  assert 0 <= d;
  assert p <= m;

  assert q - p == 2 * d + (q - p) % 2;
  assert 0 <= (q - p) % 2 < 2;

  assert d <= 2 * d;
  assert d <= 2 * d + (q - p) % 2;
  assert d <= q - p;
  assert m <= q;

  assert m - p == d;
  assert q - m == (q - p) - d;

  assert (q - m) - (m - p) == (q - p) - 2 * d;
  assert (q - m) - (m - p) == (q - p) % 2;

  assert 0 <= (q - m) - (m - p);
  assert (q - m) - (m - p) <= 1;
}
// </vc-code>

