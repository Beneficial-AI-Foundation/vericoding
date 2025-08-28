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
lemma CountLemma(hi: nat, s: seq<int>)
  requires 0 <= hi <= |s|
  ensures Count(hi, s) == |set i | 0 <= i < hi && s[i] % 2 == 0|
  decreases hi
{
  if hi == 0 {
    assert Count(hi, s) == 0;
    assert |set i | 0 <= i < hi && s[i] % 2 == 0| == 0;
  } else {
    CountLemma(hi - 1, s);
    if s[hi - 1] % 2 == 0 {
      assert Count(hi, s) == 1 + Count(hi - 1, s);
      assert |set i | 0 <= i < hi && s[i] % 2 == 0| == |set i | 0 <= i < hi - 1 && s[i] % 2 == 0| + 1;
    } else {
      assert Count(hi, s) == Count(hi - 1, s);
      assert |set i | 0 <= i < hi && s[i] % 2 == 0| == |set i | 0 <= i < hi - 1 && s[i] % 2 == 0|;
    }
  }
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
method PreComputeImpl(a: array<int>, b: array<int>) returns (p: nat)
  requires a.Length == b.Length
  modifies b
  ensures (b.Length == 0 || (a.Length == b.Length && 1 <= b.Length <= a.Length)) &&
          p == Count(b.Length, a[..])
{
  if a.Length == 0 {
    p := 0;
  } else {
    var i := 0;
    var count := 0;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant count == Count(i, a[..])
    {
      if a[i] % 2 == 0 {
        count := count + 1;
      }
      i := i + 1;
    }
    p := count;
    CountLemma(a.Length, a[..]);
    assert p == Count(a.Length, a[..]);
  }
}
// </vc-code>
