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
method ComputeCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
    decreases CountIndex
    modifies b
    ensures p == Count(CountIndex,a)
// </vc-spec>
// <vc-code>
{
  if CountIndex == 0 {
    p := 0;
    return;
  }
  var i := 0;
  p := 0;
  while i < CountIndex
    invariant 0 <= i <= CountIndex
    invariant 0 <= p <= i
    invariant p == Count(i, a)
    decreases CountIndex - i
  {
    if a[i] % 2 == 0 {
      p := p + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

