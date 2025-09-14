

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ParabolaDirectrix(a: real, h: real, k: real) returns (directrix: real)
    requires a != 0.0
    ensures directrix == k - 1.0 / (4.0 * a)
// </vc-spec>
// <vc-code>
{
  var denom := 4.0 * a;
  if a >= 0.0 {
    assert a > 0.0;
    assert denom > 0.0;
  } else {
    assert denom < 0.0;
  }
  directrix := k - 1.0 / denom;
}
// </vc-code>

