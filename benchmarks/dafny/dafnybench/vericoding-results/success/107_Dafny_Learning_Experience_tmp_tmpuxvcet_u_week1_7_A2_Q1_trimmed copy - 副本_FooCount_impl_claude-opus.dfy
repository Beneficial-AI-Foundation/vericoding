ghost function Count(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
    decreases hi
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + Count(hi-1, s) else Count(hi-1, s)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FooCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
    decreases CountIndex
    modifies b
    ensures p == Count(CountIndex,a)
// </vc-spec>
// <vc-code>
{
    if CountIndex == 0 {
        p := 0;
    } else {
        var subCount := FooCount(CountIndex - 1, a, b);
        if a[CountIndex - 1] % 2 == 0 {
            p := subCount + 1;
        } else {
            p := subCount;
        }
    }
}
// </vc-code>

