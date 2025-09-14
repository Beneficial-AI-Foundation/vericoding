// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/G4sc3

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/nujsu

// Insertion sort með hjálp helmingunarleitar.


method Search( s: seq<int>, x: int ) returns ( k: int )
    // Ekki má breyta forskilyrðum eða eftirskilyrðum fallsins
    requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
    ensures 0 <= k <= |s|;
    ensures forall i | 0 <= i < k :: s[i] <= x;
    ensures forall i | k <= i < |s| :: s[i] >= x;
    ensures forall z | z in s[..k] :: z <= x;
    ensures forall z | z in s[k..] :: z >= x;
    ensures s == s[..k]+s[k..];
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ExistsElemFromMultiset(m: multiset<int>, r: seq<int>)
  requires multiset(r) <= m
  requires |r| < |m|
  ensures exists e :: e in m - multiset(r)
{
  if !(exists e :: e in m - multiset(r)) {
    // If there is no element in m - multiset(r), then m - multiset(r) is empty
    assert m - multiset(r) == {};
    // Hence m <= multiset(r)
    assert m <= multiset(r);
    // Together with multiset(r) <= m we get equality
    assert multiset(r) == m;
    // Which implies |r| == |m|, contradicting the requirement |r| < |m|
    assert |r| == |m|;
    assert false;
  }
}
// </vc-helpers>

// <vc-spec>
method Sort( m: multiset<int> ) returns ( r: seq<int> )
    ensures multiset(r) == m;
    ensures forall p,q | 0 <= p < q < |r| :: r[p] <= r[q];
// </vc-spec>
// <vc-code>
{
  r := [];
  while |r| < |m|
    invariant 0 <= |r| <= |m|;
    invariant multiset(r) <= m;
    invariant forall p,q | 0 <= p < q < |r| :: r[p] <= r[q];
    decreases |m| - |r|;
  {
    ExistsElemFromMultiset(m, r);
    var e:int :| e in m - multiset(r);
    var k := 0;
    while k < |r| && r[k] <= e
      invariant 0 <= k <= |r|;
      invariant forall i | 0 <= i < k :: r[i] <= e;
      decreases |r| - k;
    {
      k := k + 1;
    }
    r := r[..k] + [e] + r[k..];
  }
  return r;
}
// </vc-code>

