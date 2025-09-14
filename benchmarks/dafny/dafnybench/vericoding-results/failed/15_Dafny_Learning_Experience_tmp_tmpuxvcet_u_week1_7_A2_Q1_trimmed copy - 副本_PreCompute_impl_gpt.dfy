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
lemma NatNonZeroIsAtLeastOne(n: nat)
  ensures n != 0 ==> 1 <= n
{
  if n != 0 {
    assert 1 <= n;
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
  p := 0;
  if b.Length == 0 {
  } else {
    NatNonZeroIsAtLeastOne(b.Length);
    assert 1 <= b.Length;
    assert a.Length == b.Length;
    assert b.Length <= a.Length;
  }
}
// </vc-code>

