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
lemma MultisetDecrease(m: multiset<int>, x: int)
    requires x in m
    ensures |m - multiset{x}| < |m|
{
}

lemma MultisetRemovePreservesElements(m: multiset<int>, x: int, y: int)
    requires x in m && y in m && x != y
    ensures y in (m - multiset{x})
{
}

lemma SeqMultisetRelation(s: seq<int>, m: multiset<int>, x: int)
    requires multiset(s) == m - multiset{x}
    requires x in m
    ensures multiset(s + [x]) == m
{
}

lemma SortedPreservation(s: seq<int>, x: int)
    requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
    requires forall y | y in s :: y <= x
    ensures forall p,q | 0 <= p < q < |s + [x]| :: (s + [x])[p] <= (s + [x])[q]
{
    var extended := s + [x];
    forall p, q | 0 <= p < q < |extended|
        ensures extended[p] <= extended[q]
    {
        if q < |s| {
            assert extended[p] == s[p] && extended[q] == s[q];
        } else if p < |s| && q == |s| {
            assert extended[p] == s[p] && extended[q] == x;
            assert s[p] <= x;
        }
    }
}

lemma MinPropertyForSequence(s: seq<int>, currentM: multiset<int>, min: int)
    requires min in currentM
    requires forall z | z in currentM :: min <= z
    requires forall i,j | i in multiset(s) && j in currentM :: i <= j
    ensures forall y | y in s :: y <= min
{
    forall y | y in s
        ensures y <= min
    {
        assert y in multiset(s);
        assert min in currentM;
        assert y <= min;
    }
}
// </vc-helpers>

// <vc-spec>
method Sort( m: multiset<int> ) returns ( s: seq<int> )
    // Setjið viðeigandi ensures klausur hér
    ensures multiset(s) == m;
    ensures forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
// </vc-spec>
// <vc-code>
{
    if |m| == 0 {
        return [];
    }
    
    var currentM := m;
    s := [];
    
    while |currentM| > 0
        invariant currentM + multiset(s) == m
        invariant forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
        invariant forall i,j | i in multiset(s) && j in currentM :: i <= j
        decreases |currentM|
    {
        var min := MinOfMultiset(currentM);
        MultisetDecrease(currentM, min);
        
        MinPropertyForSequence(s, currentM, min);
        
        var oldS := s;
        s := s + [min];
        currentM := currentM - multiset{min};
        
        SortedPreservation(oldS, min);
    }
}
// </vc-code>

