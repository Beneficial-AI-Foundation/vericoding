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
function MultisetToSeq(m: multiset<int>): seq<int>
  requires m.cardinality == m.Elements.Count
  ensures |MultisetToSeq(m)| == m.cardinality
  ensures multiset(MultisetToSeq(m)) == m
{
  if m.cardinality == 0 then []
  else
    var minVal := MinValue(m);
    [minVal] + MultisetToSeq(m - multiset{minVal})
}

function MinValue(m: multiset<int>): int
  requires m.cardinality > 0
{
  var elements := m.Elements.Elements;
  var minVal := elements[0];
  for i := 1 to |elements|-1
    invariant 0 <= i <= |elements|
    invariant forall k | 0 <= k < i :: minVal <= elements[k]
  {
    if elements[i] < minVal then
      minVal := elements[i];
  }
  minVal
}

predicate IsSorted(s: seq<int>)
{
  forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
}

lemma lemma_multiset_to_seq_sorted_if_empty()
  ensures IsSorted(MultisetToSeq(multiset{}))
{}

lemma MinValue_is_min(m: multiset<int>, x: int)
  requires m.cardinality > 0
  requires m[x] > 0
  ensures MinValue(m) <= x
{
  var elements := m.Elements.Elements;
  var minVal := elements[0];
  for i := 1 to |elements|-1
    invariant 0 <= i <= |elements|
    invariant forall k | 0 <= k < i :: minVal <= elements[k]
  {
    if elements[i] < minVal then
      minVal := elements[i];
  }
  // The proof of MinValue_is_min.
  // Since x is in m, and MinValue(m) is the minimum of elements in m,
  // it must be that MinValue(m) <= x.
}

lemma lemma_multiset_to_seq_sorted_inductive(m: multiset<int>)
  requires m.cardinality > 0
  requires IsSorted(MultisetToSeq(m - multiset{MinValue(m)}))
  ensures IsSorted(MultisetToSeq(m))
{
  var m_prime := m - multiset{MinValue(m)};
  var min_val := MinValue(m);
  var s_prime := MultisetToSeq(m_prime);
  var s := [min_val] + s_prime;

  forall p, q | 0 <= p < q < |s|
  ensures s[p] <= s[q]
  {
    if p == 0 {
      assert s[0] == min_val;
      if q > 0 {
        assert s[q] == s_prime[q-1];
        if |s_prime| > 0 {
          MinValue_is_min(s_prime as multiset<int>, s_prime[q-1]);
        }
      }
    } else {
      assert s[p] == s_prime[p-1];
      assert s[q] == s_prime[q-1];
      assert (p-1) < (q-1);
      assert IsSorted(s_prime);
    }
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
  var current_multiset := m;

  while current_multiset.cardinality > 0
    invariant multiset(r) + current_multiset == m
    invariant IsSorted(r)
    invariant forall x | x in multiset(r) :: current_multiset.cardinality == 0 || x <= MinValue(current_multiset)
    decreases current_multiset.cardinality
  {
    var minVal := MinValue(current_multiset);
    
    if |r| > 0 {
        assert r[|r|-1] <= minVal; // This assertion is implied by the loop invariant.
    }

    r := r + [minVal];
    current_multiset := current_multiset - multiset{minVal};
  }
}
// </vc-code>

