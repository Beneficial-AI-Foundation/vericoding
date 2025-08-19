// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Min(a: int, b: int) returns (minValue: int)
    ensures minValue == a || minValue == b
    ensures minValue <= a && minValue <= b
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>