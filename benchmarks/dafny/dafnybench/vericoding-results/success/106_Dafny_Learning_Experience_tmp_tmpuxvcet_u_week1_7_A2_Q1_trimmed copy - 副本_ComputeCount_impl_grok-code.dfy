ghost function Count(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
    decreases hi
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + Count(hi-1, s) else Count(hi-1, s)
}

// <vc-helpers>
// No changes needed
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
    return 0;
  } else {
    var p0 := ComputeCount(CountIndex - 1, a, b);
    b[CountIndex - 1] := if a[CountIndex - 1] % 2 == 0 then 1 else 0;
    if a[CountIndex - 1] % 2 == 0 {
      return 1 + p0;
    } else {
      return p0;
    }
  }
}
// </vc-code>

