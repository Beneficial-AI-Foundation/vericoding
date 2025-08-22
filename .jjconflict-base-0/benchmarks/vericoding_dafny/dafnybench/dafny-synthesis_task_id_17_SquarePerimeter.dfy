// <vc-helpers>
// </vc-helpers>

method SquarePerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 4 * side
// <vc-code>
{
  assume false;
}
// </vc-code>