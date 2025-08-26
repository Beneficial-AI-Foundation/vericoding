// The specification requires that the returned values satisfy `less <= x <= more`, meaning `less` should be less than or equal to `x`, and `more` should be greater than or equal to `x`.

// A simple implementation would be to set `less = x - y` and `more = x + y`. Since `y >= 0`, this ensures that `less <= x <= more`.

// <vc-spec>
function abs(x: int): int{
    if x>0 then x else -x
}

method MultiReturn(x:int, y:int) returns (more:int, less:int)
requires y>=0;
ensures less <= x <= more;
// </vc-spec>

// <vc-helpers>
// </vc-helpers>

// <vc-code>
{
  less := x - y;
  more := x + y;
}
// </vc-code>