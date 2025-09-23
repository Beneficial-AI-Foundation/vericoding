// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method A1(x: int, y: int) returns (r: int)
ensures r == x + y
// </vc-spec>
// <vc-code>
{
    r:= x;
    if( y < 0){
        var n:= y;
        while(n != 0)
        invariant r == x + y - n
        invariant -n >= 0
        {
            r:= r-1;
            n:= n + 1;
        }
    } else {
        var n := y;
        while(n!= 0)
        invariant r == x+ y - n
        invariant n >= 0
        {
            r:= r + 1;
            n:= n - 1;
        }
    }
}
// </vc-code>
