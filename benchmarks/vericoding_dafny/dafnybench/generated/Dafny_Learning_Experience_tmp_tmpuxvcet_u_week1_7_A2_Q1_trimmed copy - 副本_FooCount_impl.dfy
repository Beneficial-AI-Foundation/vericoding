// The `Count` function counts how many even numbers are in the first `hi` elements of sequence `s`.

// Let me analyze the requirements:
// - When `CountIndex == 0`, we should return 0 (base case)
// - When `CountIndex > 0`, we need `|a| == b.Length` and `1 <= CountIndex <= |a|`
// - The method should return the same value as `Count(CountIndex, a)`

// I'll implement this using a loop that iterates through the first `CountIndex` elements of `a` and counts the even numbers.

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
method FooCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
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
    p := 0;
    var i := 0;
    while i < CountIndex
      invariant 0 <= i <= CountIndex
      invariant p == Count(i, a)
    {
      if a[i] % 2 == 0 {
        p := p + 1;
      }
      i := i + 1;
    }
  }
}
// </vc-code>