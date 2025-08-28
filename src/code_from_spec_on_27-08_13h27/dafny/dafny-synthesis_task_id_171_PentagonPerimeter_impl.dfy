// <vc-helpers>
// No additional helpers or proofs needed for this simple calculation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method PentagonPerimeter(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 5 * side
// </vc-spec>
// </vc-spec>

// <vc-code>
method PentagonPerimeterImpl(side: int) returns (perimeter: int)
    requires side > 0
    ensures perimeter == 5 * side
{
    perimeter := 5 * side;
}
// </vc-code>
