// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method MaxSum(x:int, y:int) returns (s:int, m:int)
    ensures s == x+y
    ensures (m == x || m == y) && x <= m && y <= m
// </vc-spec>
// <vc-code>
{
    s := x+y;
    if x > y{
      m := x;
    } else if y > x{
      m := y;
    } else {
      m := x;
    }
    assert  m >= y;
}
// </vc-code>
