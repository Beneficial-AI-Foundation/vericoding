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
lemma MultisetSliceConcat(s: seq<int>, k: int)
    requires 0 <= k <= |s|
    ensures multiset(s) == multiset(s[..k]) + multiset(s[k..])
{
    if |s| == 0 {
        assert s == [];
        assert s[..k] == [];
        assert s[k..] == [];
    } else if k == 0 {
        assert s[..0] == [];
        assert s[0..] == s;
    } else if k == |s| {
        assert s[..|s|] == s;
        assert s[|s|..] == [];
    } else {
        // For the general case, we can use induction
        assert s == s[..k] + s[k..];
        // This follows from the definition of sequence slicing and concatenation
    }
}

lemma InsertPreservesMultiset(s: seq<int>, x: int, k: int)
    requires 0 <= k <= |s|
    ensures multiset(s[..k] + [x] + s[k..]) == multiset(s) + multiset{x}
{
    MultisetSliceConcat(s, k);
    assert s[..k] + [x] + s[k..] == s[..k] + ([x] + s[k..]);
    assert multiset(s[..k] + [x] + s[k..]) == multiset(s[..k]) + multiset([x] + s[k..]);
    assert multiset([x] + s[k..]) == multiset{x} + multiset(s[k..]);
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
        decreases |remaining|
        invariant multiset(r) + remaining == m
        invariant forall p,q | 0 <= p < q < |r| :: r[p] <= r[q]
    {
        var x :| x in remaining;
        var k := Search(r, x);
        
        assert 0 <= k <= |r|;
        assert forall i | 0 <= i < k :: r[i] <= x;
        assert forall i | k <= i < |r| :: r[i] >= x;
        
        var newR := r[..k] + [x] + r[k..];
        
        assert forall p,q | 0 <= p < q < k :: newR[p] <= newR[q];
        assert forall p | 0 <= p < k :: newR[p] <= x;
        assert forall q | k < q < |newR| :: x <= newR[q];
        assert forall p,q | k < p < q < |newR| :: newR[p] <= newR[q];
        
        InsertPreservesMultiset(r, x, k);
        assert multiset(newR) == multiset(r) + multiset{x};
        
        r := newR;
        remaining := remaining - multiset{x};
    }
}
// </vc-code>

