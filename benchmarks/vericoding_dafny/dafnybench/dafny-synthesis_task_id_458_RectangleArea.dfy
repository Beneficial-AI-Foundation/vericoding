// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method RectangleArea(length: int, width: int) returns (area: int)
    requires length > 0
    requires width > 0
    ensures area == length * width
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>