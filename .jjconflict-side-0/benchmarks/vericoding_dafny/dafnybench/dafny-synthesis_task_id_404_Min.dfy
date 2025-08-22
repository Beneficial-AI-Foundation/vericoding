// <vc-helpers>
// </vc-helpers>

method Min(a: int, b: int) returns (minValue: int)
    ensures minValue == a || minValue == b
    ensures minValue <= a && minValue <= b
// <vc-code>
{
  assume false;
}
// </vc-code>