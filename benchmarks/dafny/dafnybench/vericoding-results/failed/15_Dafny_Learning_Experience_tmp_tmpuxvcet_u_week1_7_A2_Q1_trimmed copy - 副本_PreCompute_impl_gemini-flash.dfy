ghost function Count(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
    decreases hi
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + Count(hi-1, s) else Count(hi-1, s)
}




method ComputeCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
    decreases CountIndex
    modifies b
    ensures p == Count(CountIndex,a)
{
  assume{:axiom} false;
}

// <vc-helpers>
function CountHelper(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
    decreases hi
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + CountHelper(hi-1, s) else CountHelper(hi-1, s)
}

method ComputeCountHelper(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
    decreases CountIndex
    modifies b
    ensures p == CountHelper(CountIndex,a)
{
    if CountIndex == 0
    {
        p := 0;
    }
    else
    {
        var temp_p: nat;
        temp_p := ComputeCountHelper(CountIndex - 1, a, b);
        if a[CountIndex-1]%2 == 0
        {
            p := 1 + temp_p;
        }
        else
        {
            p := temp_p;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method PreCompute(a:array<int>,b:array<int>)returns(p:nat)
    requires a.Length == b.Length 
    modifies b
    ensures (b.Length == 0 || (a.Length == b.Length && 1 <= b.Length <= a.Length)) &&
    forall p::p == Count(b.Length,a[..]) ==> p==Count(b.Length,a[..])
// </vc-spec>
// <vc-code>
{
    p := ComputeCountHelper(a.Length, a[..], b);
    assert p == CountHelper(a.Length, a[..]);
}
// </vc-code>

