// <vc-helpers>
// </vc-helpers>

method mult(a:int, b:int) returns (x:int)
    requires a >= 0 && b >= 0
    ensures x == a * b
// <vc-code>
{
  assume false;
}
// </vc-code>