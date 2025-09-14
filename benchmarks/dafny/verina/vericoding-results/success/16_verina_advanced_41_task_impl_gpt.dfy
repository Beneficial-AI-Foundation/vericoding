// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max2(a: int, b: int): int { if a >= b then a else b }
function max3(a: int, b: int, c: int): int { max2(max2(a, b), c) }
// </vc-helpers>

// <vc-spec>
method MaxOfThree(a: int, b: int, c: int) returns (result: int)
    ensures result >= a && result >= b && result >= c
    ensures result == a || result == b || result == c
// </vc-spec>
// <vc-code>
{
  var m: int;
  if a >= b {
    m := a;
  } else {
    m := b;
  }
  assert m >= a && m >= b;
  assert m == a || m == b;
  if m >= c {
    result := m;
  } else {
    assert c >= m;
    assert c >= a && c >= b;
    result := c;
  }
}
// </vc-code>
