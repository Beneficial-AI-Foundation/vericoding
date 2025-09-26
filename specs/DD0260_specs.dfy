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
method Max(x:int, y:int) returns (a:int)
ensures a == x || a == y;
ensures x > y ==> a == x;
ensures x <= y ==> a == y;
// </vc-spec>
// <vc-code>
{
    if ( x > y ) 
    { 
        a := x;
    } else 
    { 
        a := y; 
    }
}
// </vc-code>
