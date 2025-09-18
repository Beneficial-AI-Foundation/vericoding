// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function FirstComponent(x: int, y: int): int { x + y }
function SecondComponent(x: int, y: int): int { x - y }
// </vc-helpers>

// <vc-spec>
method MultipleReturns(x: int, y: int) returns (result: (int, int))
    ensures result.0 == x + y
    ensures result.1 + y == x
// </vc-spec>
// <vc-code>
{
    result := (FirstComponent(x, y), SecondComponent(x, y));
}
// </vc-code>
