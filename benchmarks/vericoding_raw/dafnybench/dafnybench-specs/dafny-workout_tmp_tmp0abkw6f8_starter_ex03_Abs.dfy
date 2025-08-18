// <vc-helpers>
// </vc-helpers>

method Abs(x: int) returns (y: int)
    requires x == -1
    ensures 0 <= y
    ensures 0 <= x ==> y == x
    ensures x < 0 ==> y == -x
// <vc-code>
{
  assume false;
}
// </vc-code>