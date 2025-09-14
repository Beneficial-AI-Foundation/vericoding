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
lemma LemmaMultisetUpTo(r: seq<int>, s: seq<int>, k: int, x: int)
  requires 0 <= k <= |s|
  requires r == s[..k] + [x] + s[k..]
  ensures multiset(r) == multiset(s) + multiset{x}
{
}

lemma LemmaMultisetInsert(s: seq<int>, x: int, k: int)
  requires 0 <= k <= |s|
  requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
  ensures multiset(s[..k] + [x] + s[k..]) == multiset(s) + multiset{x}
{
}

ghost predicate IsSorted(s: seq<int>) {
  forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
}

lemma LemmaMultisetSortedSequence(m': multiset<int>) 
  ensures exists s' :: multiset(s') == m' && IsSorted(s')
{
}
// </vc-helpers>

// <vc-spec>
method Sort( m: multiset<int> ) returns ( r: seq<int> )
    ensures multiset(r) == m;
    ensures forall p,q | 0 <= p < q < |r| :: r[p] <= r[q];
// </vc-spec>
// <vc-code>
{
  if m == multiset{} {
    r := [];
  } else {
    var x :| x in m;
    var m' := m - multiset{x};
    var s' :| multiset(s') == m' && IsSorted(s');
    r := Sort(m');
    var k := Search(r, x);
    r := r[..k] + [x] + r[k..];
    LemmaMultisetInsert(r, x, k);
  }
}
// </vc-code>

