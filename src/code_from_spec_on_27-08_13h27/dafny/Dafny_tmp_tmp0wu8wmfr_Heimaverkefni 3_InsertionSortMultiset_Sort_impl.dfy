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
// Helper lemma to prove properties about sequences and multisets
lemma MultisetPreservation(s: seq<int>, i: int, j: int)
  requires 0 <= i <= j <= |s|
  ensures multiset(s[..i] + s[i..j] + s[j..]) == multiset(s)
{
  // Dafny can prove this automatically for valid indices
}

// Helper lemma to ensure the sorted property during insertion
lemma SortedInsertion(s: seq<int>, x: int, k: int)
  requires 0 <= k <= |s|
  requires forall p, q | 0 <= p < q < |s| :: s[p] <= s[q]
  requires forall i | 0 <= i < k :: s[i] <= x
  requires forall i | k <= i < |s| :: s[i] >= x
  ensures forall p, q | 0 <= p < q < |s[..k] + [x] + s[k..]| :: (s[..k] + [x] + s[k..])[p] <= (s[..k] + [x] + s[k..])[q]
{
  // Dafny can often prove sortedness with proper invariants
}

// Helper method for binary search implementation
method BinarySearch(s: seq<int>, x: int) returns (k: int)
  requires forall p, q | 0 <= p < q < |s| :: s[p] <= s[q]
  ensures 0 <= k <= |s|
  ensures forall i | 0 <= i < k :: s[i] <= x
  ensures forall i | k <= i < |s| :: s[i] >= x
  ensures forall z | z in s[..k] :: z <= x
  ensures forall z | z in s[k..] :: z >= x
  ensures s == s[..k] + s[k..]
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
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Sort( m: multiset<int> ) returns ( r: seq<int> )
    ensures multiset(r) == m;
    ensures forall p,q | 0 <= p < q < |r| :: r[p] <= r[q];
// </vc-spec>
// </vc-spec>

// <vc-code>
method InsertionSort(m: multiset<int>) returns (r: seq<int>)
  ensures multiset(r) == m
  ensures forall p, q | 0 <= p < q < |r| :: r[p] <= r[q]
{
  r := [];
  var remaining := m;
  while remaining != multiset({})
    decreases |remaining|
    invariant multiset(r) + remaining == m
    invariant forall p, q | 0 <= p < q < |r| :: r[p] <= r[q]
  {
    var x :| x in remaining;
    remaining := remaining - multiset{x};
    var k := BinarySearch(r, x);
    var old_r := r;
    r := r[..k] + [x] + r[k..];
    // Assert and prove the multiset property after each insertion
    calc {
      multiset(r);
      == multiset(r[..k] + [x] + r[k..]);
      == multiset(r[..k]) + multiset([x]) + multiset(r[k..]);
      == multiset(old_r[..k]) + multiset([x]) + multiset(old_r[k..]);
      == multiset(old_r) + multiset([x]);
      == multiset(old_r) + multiset{x};
    }
    // Use the lemma to ensure sortedness after insertion
    SortedInsertion(old_r, x, k);
  }
}
// </vc-code>
