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
function Count_Compute(hi: nat, s:seq<int>): nat
    requires 0 <= hi <= |s|
    decreases hi
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + Count_Compute(hi-1, s) else Count_Compute(hi-1, s)
}

lemma CountEquivalence(a: array<int>)
    requires a.Length >= 0
    ensures a.Length == 0 ==> Count(a.Length, a[..]) == Count(0, a[..])
    ensures a.Length > 0 ==> Count(a.Length, a[..]) == Count(a.Length, a[..])
    ensures Count_Compute(a.Length, a[..]) == Count(a.Length, a[..])
{
    if a.Length == 0 {
        assert Count(0, a[..]) == 0;
        assert Count_Compute(0, a[..]) == 0;
    }
    CountComputeEquivalence(a.Length, a[..]);
}

lemma CountComputeEquivalence(hi: nat, s: seq<int>)
    requires 0 <= hi <= |s|
    ensures Count_Compute(hi, s) == Count(hi, s)
    decreases hi
{
    if hi == 0 {
        assert Count_Compute(0, s) == 0;
        assert Count(0, s) == 0;
    } else {
        CountComputeEquivalence(hi-1, s);
        if s[hi-1]%2 == 0 {
            assert Count_Compute(hi, s) == 1 + Count_Compute(hi-1, s);
            assert Count(hi, s) == 1 + Count(hi-1, s);
        } else {
            assert Count_Compute(hi, s) == Count_Compute(hi-1, s);
            assert Count(hi, s) == Count(hi-1, s);
        }
    }
}

lemma ArraySliceProperty(a: array<int>)
    requires a.Length >= 0
    ensures |a[..]| == a.Length
{
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
    ArraySliceProperty(a);
    CountEquivalence(a);
    
    if a.Length == 0 {
        p := 0;
    } else {
        p := Count_Compute(a.Length, a[..]) as nat;
    }
    
    return p;
}
// </vc-code>

