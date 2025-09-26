// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Two(x: int) returns (y: int)
ensures y == x + 1
// </vc-spec>
// <vc-code>
{
    assert true;
    var a:= x+1;
    assert (a - 1 == 0 ==> x == 0) && (x - 1!= 0 ==> a == x +1);
    if(a - 1 == 0){
        y:= 1;
    } else {
        y:= a;
    }
}
// </vc-code>
