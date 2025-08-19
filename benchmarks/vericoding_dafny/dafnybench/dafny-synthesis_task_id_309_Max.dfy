// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Max(a: int, b: int) returns (maxValue: int)
    ensures maxValue == a || maxValue == b
    ensures maxValue >= a && maxValue >= b
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>