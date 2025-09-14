// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
lemma CountIsNonNegative(hi: nat, s: seq<int>)
  requires 0 <= hi <= |s|
  ensures Count(hi, s) >= 0
  decreases hi
{
  if hi > 0 {
    CountIsNonNegative(hi - 1, s);
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
  var i: nat := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant p == Count(i, a[..])
    invariant forall k :: 0 <= k < i ==> b[k] == Count(k + 1, a[..])
  {
    if a[i] % 2 == 0 {
      p := p + 1;
    }
    b[i] := p;
    i := i + 1;
    CountIsNonNegative(i, a[..]);
  }
}
// </vc-code>
