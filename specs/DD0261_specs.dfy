// <vc-preamble>
function abs(x: int): int{
    if x>0 then x else -x
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method MultiReturn(x:int, y:int) returns (more:int, less:int)
requires y>=0;
ensures less <= x <= more;
// </vc-spec>
// <vc-code>
{
    more := x + y;
    less := x - y;
}
// </vc-code>
