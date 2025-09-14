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
lemma MultisetSliceProperty(s: seq<int>, k: int)
    requires 0 <= k <= |s|
    ensures multiset(s[..k]) + multiset(s[k..]) == multiset(s)
{
    if k == 0 {
        assert s[..k] == [];
        assert s[k..] == s;
        assert multiset(s[..k]) == multiset{};
    } else if k == |s| {
        assert s[..k] == s;
        assert s[k..] == [];
        assert multiset(s[k..]) == multiset{};
    } else {
        assert s == s[..k] + s[k..];
        assert multiset(s[..k] + s[k..]) == multiset(s[..k]) + multiset(s[k..]);
    }
}

lemma MultisetInsertPreservation(s: seq<int>, x: int, k: int)
    requires 0 <= k <= |s|
    ensures multiset(s[..k] + [x] + s[k..]) == multiset(s) + multiset{x}
{
    assert s[..k] + [x] + s[k..] == s[..k] + ([x] + s[k..]);
    assert multiset(s[..k] + ([x] + s[k..])) == multiset(s[..k]) + multiset([x] + s[k..]);
    assert multiset([x] + s[k..]) == multiset{x} + multiset(s[k..]);
    MultisetSliceProperty(s, k);
    assert multiset(s[..k]) + multiset(s[k..]) == multiset(s);
}

lemma SortedInsertPreservation(s: seq<int>, x: int, k: int)
    requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
    requires 0 <= k <= |s|
    requires forall i | 0 <= i < k :: s[i] <= x
    requires forall i | k <= i < |s| :: s[i] >= x
    ensures forall p,q | 0 <= p < q < |s[..k] + [x] + s[k..]| :: (s[..k] + [x] + s[k..])[p] <= (s[..k] + [x] + s[k..])[q]
{
    var result := s[..k] + [x] + s[k..];
    forall p,q | 0 <= p < q < |result|
        ensures result[p] <= result[q]
    {
        if p < k && q < k {
            assert result[p] == s[p] && result[q] == s[q];
        } else if p < k && q == k {
            assert result[p] == s[p] && result[q] == x;
            assert s[p] <= x;
        } else if p < k && q > k {
            assert result[p] == s[p] && result[q] == s[q-1];
            assert s[p] <= x && x <= s[q-1];
        } else if p == k && q > k {
            assert result[p] == x && result[q] == s[q-1];
            assert x <= s[q-1];
        } else if p > k && q > k {
            assert result[p] == s[p-1] && result[q] == s[q-1];
            assert s[p-1] <= s[q-1];
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
    var remaining := m;
    
    while remaining != multiset{}
        invariant multiset(r) + remaining == m
        invariant forall p,q | 0 <= p < q < |r| :: r[p] <= r[q]
        decreases |remaining|
    {
        var x :| x in remaining;
        remaining := remaining - multiset{x};
        
        var k := Search(r, x);
        
        MultisetInsertPreservation(r, x, k);
        SortedInsertPreservation(r, x, k);
        
        r := r[..k] + [x] + r[k..];
    }
}
// </vc-code>

