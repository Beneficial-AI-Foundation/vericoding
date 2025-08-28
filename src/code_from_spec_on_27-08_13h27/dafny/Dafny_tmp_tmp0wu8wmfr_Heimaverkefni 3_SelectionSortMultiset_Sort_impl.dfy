// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/dtcnY

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/ybUCz

///////////////////////////////////////////////////////////////
// Hér byrjar óbreytanlegi hluti skrárinnar.
// Fyrir aftan þann hluta er sá hluti sem þið eigið að breyta.
///////////////////////////////////////////////////////////////

// Hjálparfall sem finnur minnsta gildi í poka

method MinOfMultiset( m: multiset<int> ) returns( min: int )
    ensures min in m;
    ensures forall z | z in m :: min <= z;
{
  assume{:axiom} false;
}

// Ekki má breyta þessu falli.


///////////////////////////////////////////////////////////////
// Hér lýkur óbreytanlega hluta skrárinnar.
// Hér fyrir aftan er sá hluti sem þið eigið að breyta til að
// útfæra afbrigði af selection sort.
///////////////////////////////////////////////////////////////

// Selection sort sem raðar poka í runu.
// Klárið að forrita þetta fall.

// <vc-helpers>
// Helper lemma to prove properties about sequences and multisets
lemma MultisetPreservation(s: seq<int>, m: multiset<int>, min: int, remaining: multiset<int>)
    ensures multiset(s + [min]) == multiset(s) + multiset{min}
    ensures remaining == m - multiset{min} ==> multiset(s + [min]) == multiset(s) + (m - remaining)
{
}

// Helper lemma to ensure sorted property of a sequence
lemma SortedProperty(s: seq<int>, min: int, m: multiset<int>)
    requires min in m
    requires forall z | z in m :: min <= z
    requires forall p, q | 0 <= p < q < |s| :: s[p] <= s[q]
    ensures forall p, q | 0 <= p < q < |s| + 1 :: (s + [min])[p] <= (s + [min])[q]
{
    forall p, q | 0 <= p < q < |s| + 1
        ensures (s + [min])[p] <= (s + [min])[q]
    {
        if q < |s| {
            assert (s + [min])[p] == s[p];
            assert (s + [min])[q] == s[q];
            assert s[p] <= s[q];
        } else if q == |s| {
            if p < |s| {
                assert (s + [min])[p] == s[p];
                assert (s + [min])[q] == min;
                assert s[p] <= min;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Sort( m: multiset<int> ) returns ( s: seq<int> )
    // Setjið viðeigandi ensures klausur hér
    ensures multiset(s) == m;
    ensures forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
// </vc-spec>
// </vc-spec>

// <vc-code>
method SelectionSort(m: multiset<int>) returns (s: seq<int>)
    ensures multiset(s) == m
    ensures forall p, q | 0 <= p < q < |s| :: s[p] <= s[q]
{
    var remaining := m;
    s := [];
    while remaining != multiset{}
        decreases |remaining|
    {
        var min := MinOfMultiset(remaining);
        SortedProperty(s, min, remaining);
        s := s + [min];
        MultisetPreservation(s, m, min, remaining);
        remaining := remaining - multiset{min};
    }
    assert multiset(s) == m;
}
// </vc-code>
