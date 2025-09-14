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
lemma {:auto} QuantifierWithTrigger(a: array<int>, b: array<int>)
    requires a.Length == b.Length
    ensures forall p :: p == Count(b.Length, a[..]) ==> p == Count(b.Length, a[..])
{
}

lemma CountStep(s: seq<int>, i: nat)
    requires 0 <= i < |s|
    ensures Count(i+1, s) == (if s[i] % 2 == 0 then 1 + Count(i, s) else Count(i, s))
    decreases i
{
    assert Count(i+1, s) == (if s[i] % 2 == 0 then 1 + Count(i, s) else Count(i, s));
}

lemma CountBound(s: seq<int>, hi: nat)
    requires 0 <= hi <= |s|
    ensures Count(hi, s) <= hi
    decreases hi
{
    if hi == 0 {
        // Count(0, s) == 0 by definition
        assert Count(0, s) == 0;
    } else {
        CountBound(s, hi - 1);
        CountStep(s, hi - 1);
        if s[hi - 1] % 2 == 0 {
            assert Count(hi, s) == 1 + Count(hi - 1, s);
            assert Count(hi, s) <= hi;
        } else {
            assert Count(hi, s) == Count(hi - 1, s);
            assert Count(hi, s) <= hi - 1;
            assert Count(hi, s) <= hi;
        }
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
  var cnt := 0;
  var i := 0;
  while i < b.Length
    invariant 0 <= i <= b.Length
    invariant 0 <= cnt <= i
    invariant cnt == Count(i, a[..])
  {
    var oldi := i;
    var oldcnt := cnt;
    if a[oldi] % 2 == 0 {
      cnt := oldcnt + 1;
    } else {
      cnt := oldcnt;
    }
    // Relate cnt to Count(oldi+1, a)
    CountStep(a[..], oldi);
    if a[oldi] % 2 == 0 {
      // then Count(oldi+1,a) == 1 + Count(oldi,a) and cnt == oldcnt + 1 == 1 + Count(oldi,a)
      assert cnt == Count(oldi + 1, a[..]);
    } else {
      // then Count(oldi+1,a) == Count(oldi,a) and cnt == oldcnt == Count(oldi,a)
      assert cnt == Count(oldi + 1, a[..]);
    }
    i := i + 1;
    // Now i == oldi+1, so cnt == Count(i, a)
    assert cnt == Count(i, a[..]);
    // And Count(i, a) <= i
    CountBound(a[..], i);
    assert cnt <= i;
  }
  p := cnt;
  return p;
}
// </vc-code>

