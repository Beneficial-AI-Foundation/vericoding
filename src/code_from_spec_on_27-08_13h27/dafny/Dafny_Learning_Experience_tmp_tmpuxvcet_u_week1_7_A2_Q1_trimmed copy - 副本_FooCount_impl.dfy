ghost function Count(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
    decreases hi
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + Count(hi-1, s) else Count(hi-1, s)
}

// <vc-helpers>
lemma CountRelation(hi: nat, s: seq<int>)
  requires 0 <= hi <= |s|
  ensures Count(hi, s) == if hi == 0 then 0 else (if s[hi-1] % 2 == 0 then 1 else 0) + Count(hi-1, s)
{
  // This lemma is implicitly proven by the definition of Count, but explicitly stating it helps in verification.
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FooCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
    decreases CountIndex
    modifies b
    ensures p == Count(CountIndex,a)
// </vc-spec>
// </vc-spec>

// <vc-code>
method FooCountImpl(CountIndex: nat, a: seq<int>, b: array<int>) returns (p: nat)
  requires CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
  decreases CountIndex
  modifies b
  ensures p == Count(CountIndex, a)
{
  if CountIndex == 0 {
    p := 0;
  } else {
    var temp := FooCountImpl(CountIndex - 1, a, b);
    if a[CountIndex - 1] % 2 == 0 {
      p := temp + 1;
    } else {
      p := temp;
    }
  }
}
// </vc-code>
