// <vc-preamble>
ghost function Count(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
    decreases hi
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + Count(hi-1, s) else Count(hi-1, s)
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Mult(x:int, y:int) returns (r:int)
    requires x>= 0 && y>=0
    decreases x
    ensures r == x*y
// </vc-spec>
// <vc-code>
{
    if x==0 {
        r:=0;
    }else{
        assert x-1>= 0 && y>= 0&& (x-1)*y + y== x*y;
        var z:= Mult(x-1,y);
        assert z+y == x*y;
        r:=z+y;
        assert r == x*y;
    }
}
// </vc-code>
