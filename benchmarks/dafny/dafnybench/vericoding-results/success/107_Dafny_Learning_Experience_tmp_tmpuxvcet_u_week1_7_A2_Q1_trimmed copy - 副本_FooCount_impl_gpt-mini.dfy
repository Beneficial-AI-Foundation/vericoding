ghost function Count(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
    decreases hi
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + Count(hi-1, s) else Count(hi-1, s)
}

// <vc-helpers>
lemma CountUnfold(hi: nat, s: seq<int>)
  requires 0 < hi <= |s|
  ensures Count(hi,s) == (if s[hi-1] % 2 == 0 then 1 + Count(hi-1,s) else Count(hi-1,s))
{
  // The equality follows by unfolding the definition of Count.
  if hi > 1 {
    CountUnfold(hi-1, s);
  }
}

lemma CountNonneg(hi: nat, s: seq<int>)
  requires 0 <= hi <= |s|
  ensures 0 <= Count(hi,s)
{
  if hi == 0 {
    // Count(0, s) == 0
  } else {
    // By induction Count(hi-1,s) >= 0
    CountNonneg(hi-1, s);
    // And Count(hi,s) is either Count(hi-1,s) or 1+Count(hi-1,s)
    CountUnfold(hi, s);
  }
}
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
  var i := 0;
  var c := 0;
  // Loop over first CountIndex elements, maintaining c == Count(i,a)
  while i < CountIndex
    invariant 0 <= i <= CountIndex
    invariant 0 <= c
    invariant c == Count(i,a)
    decreases CountIndex - i
  {
    // Safe to access a[i] because if CountIndex > 0 then precondition ensures CountIndex <= |a|
    if a[i] % 2 == 0 {
      c := c + 1;
      // establish relation for Count(i+1,a)
      CountUnfold(i+1, a);
      assert c == Count(i+1, a);
    } else {
      CountUnfold(i+1, a);
      assert c == Count(i+1, a);
    }
    i := i + 1;
  }
  // c == Count(CountIndex, a)
  return c;
}
// </vc-code>

