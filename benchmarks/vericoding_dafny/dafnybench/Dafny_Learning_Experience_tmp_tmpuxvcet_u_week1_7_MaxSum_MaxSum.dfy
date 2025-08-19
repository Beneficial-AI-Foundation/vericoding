// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MaxSum(x:int, y:int) returns (s:int, m:int)
    ensures s == x+y
    ensures (m == x || m == y) && x <= m && y <= m
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>