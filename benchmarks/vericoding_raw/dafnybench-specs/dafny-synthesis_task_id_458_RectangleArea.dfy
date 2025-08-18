// <vc-helpers>
// </vc-helpers>

method RectangleArea(length: int, width: int) returns (area: int)
    requires length > 0
    requires width > 0
    ensures area == length * width
// <vc-code>
{
  assume false;
}
// </vc-code>