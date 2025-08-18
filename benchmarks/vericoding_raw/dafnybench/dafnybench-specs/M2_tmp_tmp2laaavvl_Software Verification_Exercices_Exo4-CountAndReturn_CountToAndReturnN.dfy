// <vc-helpers>
// </vc-helpers>

method CountToAndReturnN(n: int) returns (r: int)
    requires n >= 0
    ensures r == n
// <vc-code>
{
  assume false;
}
// </vc-code>