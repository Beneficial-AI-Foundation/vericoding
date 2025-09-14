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
lemma CountProperty(hi: nat, s: seq<int>)
    requires 0 <= hi <= |s|
    ensures Count(hi, s) >= 0
    decreases hi
{
    if hi == 0 {
    } else {
        CountProperty(hi-1, s);
    }
}

lemma CountZero(s: seq<int>)
    ensures Count(0, s) == 0
{
    // Follows directly from the definition of Count
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
    if a.Length == 0 {
        p := 0;
        CountZero(a[..]);
        assert b.Length == 0;  // From precondition a.Length == b.Length
        assert Count(b.Length, a[..]) == Count(0, a[..]) == 0;
    } else {
        p := ComputeCount(a.Length, a[..], b);
        // ComputeCount ensures p == Count(a.Length, a[..])
        assert a.Length == b.Length;  // From precondition
        // Therefore p == Count(b.Length, a[..])
    }
    
    // Establish the postcondition explicitly
    assert p == Count(b.Length, a[..]);
    return p;
}
// </vc-code>

