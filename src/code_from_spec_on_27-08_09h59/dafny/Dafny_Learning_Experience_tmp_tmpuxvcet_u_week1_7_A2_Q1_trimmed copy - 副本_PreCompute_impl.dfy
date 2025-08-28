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
lemma CountEquivalence(a: array<int>)
    ensures Count(a.Length, a[..]) == Count(a.Length, a[..])
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method PreCompute(a:array<int>,b:array<int>)returns(p:nat)
    requires a.Length == b.Length 
    modifies b
    ensures (b.Length == 0 || (a.Length == b.Length && 1 <= b.Length <= a.Length)) &&
    forall p::p == Count(b.Length,a[..]) ==> p==Count(b.Length,a[..])
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if a.Length == 0 {
        p := 0;
        return p;
    }
    p := ComputeCount(a.Length, a[..], b);
    return p;
}
// </vc-code>
