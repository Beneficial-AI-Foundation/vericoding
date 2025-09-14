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
predicate SortedSeq(s: seq<int>)
{
  forall p,q :: 0 <= p < q < |s| ==> s[p] <= s[q]
}

lemma InsertMaintainsSorted(s: seq<int>, k: int, x: int)
  requires 0 <= k <= |s|
  requires forall p,q :: 0 <= p < q < |s| ==> s[p] <= s[q]
  requires forall i :: 0 <= i < k ==> s[i] <= x
  requires forall i :: k <= i < |s| ==> s[i] >= x
  ensures forall p,q :: 0 <= p < q < |s| + 1 ==> (s[..k] + [x] + s[k..])[p] <= (s[..k] + [x] + s[k..])[q]
{
  var a := s[..k];
  var b := s[k..];
  var t := a + [x] + b;
  assert |a| == k;
  assert |b| == |s| - k;
  assert |t| == |s| + 1;

  assert forall p,q :: 0 <= p < q < |t| ==> t[p] <= t[q] {
    if q < k {
      assert t[p] == a[p];
      assert t[q] == a[q];
      assert a[p] == s[p];
      assert a[q] == s[q];
      assert s[p] <= s[q];
    } else if p < k && q == k {
      assert t[p] == a[p];
      assert a[p] == s[p];
      assert t[q] == x;
      assert s[p] <= x;
    } else if p < k && q > k {
      assert q - 1 < |s|;
      assert t[p] == a[p];
      assert a[p] == s[p];
      assert q >= k + 1;
      assert q - (k + 1) < |b|;  // since q - 1 < |s| => q - (k + 1) < |s
// </vc-helpers>

// <vc-spec>
method Sort( m: multiset<int> ) returns ( r: seq<int> )
    ensures multiset(r) == m;
    ensures forall p,q | 0 <= p < q < |r| :: r[p] <= r[q];
// </vc-spec>
// <vc-code>
predicate SortedSeq(s: seq<int>)
{
  forall p,q :: 0 <= p < q < |s| ==> s[p] <= s[q]
}

lemma InsertMaintainsSorted(s: seq<int>, k: int, x: int)
  requires 0 <= k <= |s|
  requires forall p,q :: 0 <= p < q < |s| ==> s[p] <= s[q]
  requires forall i :: 0 <= i < k ==> s[i] <= x
  requires forall i :: k <= i < |s| ==> s[i] >= x
  ensures forall p,q :: 0 <= p < q < |s| + 1 ==> (s[..k] + [x] + s[k..])[p] <= (s[..k] + [x] + s[k..])[q]
{
  var a := s[..k];
  var b := s[k..];
  var t := a + [x] + b;
  assert |a| == k;
  assert |b| == |s| - k;
  assert |t| == |s| + 1;

  assert forall p,q :: 0 <= p < q < |t| ==> t[p] <= t[q] {
    if q < k {
      assert t[p] == a[p];
      assert t[q] == a[q];
      assert a[p] == s[p];
      assert a[q] == s[q];
      assert s[p] <= s[q];
    } else if p < k && q == k {
      assert t[p] == a[p];
      assert a[p] == s[p];
      assert t[q] == x;
      assert s[p] <= x;
    } else if p < k && q > k {
      assert q - 1 < |s|;
      assert t[p] == a[p];
      assert a[p] == s[p];
      assert q >= k + 1;
      assert q - (k + 1) < |b|;  // since q - 1 < |s| => q - (k + 1) < |s
// </vc-code>

