

// <vc-helpers>
// (no helper code needed)
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
  var d := q - p;
  var k := d / 2;
  m := p + k;
  var r := d % 2;
  assert d == 2 * k + r;
  assert 0 <= r && r < 2;
  assert p <= m;
  assert m <= q;
  assert 2 * k <= d;
  assert k <= d - k;
  assert 0 <= (d - k) - k && (d - k) - k <= 1;
}
// </vc-code>

