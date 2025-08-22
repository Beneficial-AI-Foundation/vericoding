// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/dtcnY

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/ybUCz

///////////////////////////////////////////////////////////////
// Hér byrjar óbreytanlegi hluti skrárinnar.
// Fyrir aftan þann hluta er sá hluti sem þið eigið að breyta.
///////////////////////////////////////////////////////////////

// Hjálparfall sem finnur minnsta gildi í poka
//ATOM MinOfMultiset
method MinOfMultiset( m: multiset<int> ) returns( min: int )
    requires m != multiset{}
    ensures min in m;
    ensures forall z | z in m :: min <= z;
{
    min :| min in m;
    var done := multiset{min};
    var m' := m-done;
    while m' != multiset{}
    {
        var z :| z in m';
        done := done+multiset{z};
        m' := m'-multiset{z};
        if z < min { min := z; }
    }
}

///////////////////////////////////////////////////////////////
// Hér lýkur óbreytanlega hluta skrárinnar.
// Hér fyrir aftan er sá hluti sem þið eigið að breyta til að
// útfæra afbrigði af selection sort.
///////////////////////////////////////////////////////////////

// Selection sort sem raðar poka í runu.
// Klárið að forrita þetta fall.
//IMPL Sort
method Sort( m: multiset<int> ) returns ( s: seq<int> )
    // Setjið viðeigandi ensures klausur hér
    ensures multiset(s) == m;
    ensures forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
{
    s := [];
    var remaining := m;
    
    while remaining != multiset{}
        invariant multiset(s) + remaining == m
        invariant forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
        invariant forall i | 0 <= i < |s| :: forall x | x in remaining :: s[i] <= x
        /* code modified by LLM (iteration 1): added decreases clause for termination */
        decreases |remaining|
    {
        var min := MinOfMultiset(remaining);
        
        /* code modified by LLM (iteration 1): simplified assertions focusing on key properties */
        assert min in remaining;
        assert forall x | x in remaining :: min <= x;
        assert forall i | 0 <= i < |s| :: s[i] <= min;
        
        s := s + [min];
        remaining := remaining - multiset{min};
        
        /* code modified by LLM (iteration 1): added assertion to help with multiset arithmetic */
        assert multiset(s[..|s|-1]) + multiset{min} + remaining == m;
    }
}