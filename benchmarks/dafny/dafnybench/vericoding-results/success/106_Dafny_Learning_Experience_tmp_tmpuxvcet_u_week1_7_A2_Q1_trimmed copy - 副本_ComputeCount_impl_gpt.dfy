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
  } else {
    var i:nat := 0;
    var c:nat := 0;
    while i < CountIndex
      invariant 0 <= i <= CountIndex
      invariant |a| == b.Length && 1 <= CountIndex <= |a|
      invariant c == Count(i, a)
      decreases CountIndex - i
    {
      assert i < |a|;
      var oldI := i;
      var oldC := c;
      if a[oldI] % 2 == 0 {
        c := c + 1;
      }
      i := oldI + 1;
      assert i > 0;
      assert i <= |a|;
      assert Count(i, a) == (if a[i - 1] % 2 == 0 then 1 + Count(i - 1, a) else Count(i - 1, a));
      assert i - 1 == oldI;
      assert Count(i - 1, a) == Count(oldI, a);
      if a[oldI] % 2 == 0 {
        assert c == oldC + 1;
      } else {
        assert c == oldC;
      }
      assert c == (if a[oldI] % 2 == 0 then 1 + Count(oldI, a) else Count(oldI, a));
      assert c == Count(i, a);
    }
    assert i == CountIndex;
    p := c;
  }
}
// </vc-code>

