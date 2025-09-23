// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method SquarePerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 4 * side
// </vc-spec>
// <vc-code>
{
    perimeter := 4 * side;
}
// </vc-code>
