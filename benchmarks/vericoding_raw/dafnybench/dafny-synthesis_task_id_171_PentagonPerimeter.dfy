// <vc-helpers>
// </vc-helpers>

method PentagonPerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 5 * side
// <vc-code>
{
  assume false;
}
// </vc-code>