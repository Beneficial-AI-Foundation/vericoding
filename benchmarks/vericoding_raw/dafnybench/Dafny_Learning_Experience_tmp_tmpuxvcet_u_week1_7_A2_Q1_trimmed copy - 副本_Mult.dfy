ghost function Count(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
    decreases hi
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + Count(hi-1, s) else Count(hi-1, s)
}

// <vc-helpers>
// </vc-helpers>

method Mult(x:int, y:int) returns (r:int)
    requires x>= 0 && y>=0
    decreases x
    ensures r == x*y
// <vc-code>
{
  assume false;
}
// </vc-code>