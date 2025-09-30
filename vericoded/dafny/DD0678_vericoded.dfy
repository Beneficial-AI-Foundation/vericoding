

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method PentagonPerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 5 * side
// </vc-spec>
// <vc-code>
{
    perimeter := 5 * side;
}
// </vc-code>

