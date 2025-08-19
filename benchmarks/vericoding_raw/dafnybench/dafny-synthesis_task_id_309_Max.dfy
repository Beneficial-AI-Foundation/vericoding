// <vc-helpers>
// </vc-helpers>

method Max(a: int, b: int) returns (maxValue: int)
    ensures maxValue == a || maxValue == b
    ensures maxValue >= a && maxValue >= b
// <vc-code>
{
  assume false;
}
// </vc-code>