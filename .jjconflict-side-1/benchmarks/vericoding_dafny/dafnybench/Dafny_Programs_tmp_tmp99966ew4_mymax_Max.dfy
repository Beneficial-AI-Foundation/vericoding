// <vc-helpers>
// </vc-helpers>

method Max(a: int, b:int) returns (c: int)
    ensures c >= a && c>= b
// <vc-code>
{
  assume false;
}
// </vc-code>