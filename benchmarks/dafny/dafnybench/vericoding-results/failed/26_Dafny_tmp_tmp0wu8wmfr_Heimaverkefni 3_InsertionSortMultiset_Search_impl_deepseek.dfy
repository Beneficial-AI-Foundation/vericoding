// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/G4sc3

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/nujsu

// Insertion sort með hjálp helmingunarleitar.

// <vc-helpers>
lemma BinarySearchLemma(s: seq<int>, x: int, low: int, high: int, k: int)
  requires forall p, q | 0 <= p < q < |s| :: s[p] <= s[q]
  requires 0 <= low <= high <= |s|
  requires forall i | 0 <= i < low :: s[i] <= x
  requires forall i | high <= i < |s| :: s[i] >= x
  ensures 0 <= k <= |s|
  ensures forall i | 0 <= i < k :: s[i] <= x
  ensures forall i | k <= i < |s| :: s[i] >= x
{
}
// </vc-helpers>

// <vc-spec>
method Search( s: seq<int>, x: int ) returns ( k: int )
    // Ekki má breyta forskilyrðum eða eftirskilyrðum fallsins
    requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
    ensures 0 <= k <= |s|;
    ensures forall i | 0 <= i < k :: s[i] <= x;
    ensures forall i | k <= i < |s| :: s[i] >= x;
    ensures forall z | z in s[..k] :: z <= x;
    ensures forall z | z in s[k..] :: z >= x;
    ensures s == s[..k]+s[k..];
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := |s|;
  
  while low < high
    invariant 0 <= low <= high <= |s|
    invariant forall i | 0 <= i < low :: s[i] <= x
    invariant forall i | high <= i < |s| :: s[i] >= x
  {
    var mid := (low + high) / 2;
    if s[mid] <= x {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  
  k := low;
  assert 0 <= k <= |s|;
  assert forall i | 0 <= i < k :: s[i] <= x;
  assert forall i | k <= i < |s| :: s[i] >= x;
  assert forall z | z in s[..k] :: z <= x;
  assert forall z | z in s[k..] :: z >= x;
  assert s == s[..k] + s[k..];
}
// </vc-code>

