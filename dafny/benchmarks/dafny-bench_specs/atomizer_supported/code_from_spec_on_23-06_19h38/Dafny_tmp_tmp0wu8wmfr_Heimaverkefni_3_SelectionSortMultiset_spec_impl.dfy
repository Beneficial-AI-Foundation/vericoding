// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/dtcnY

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/ybUCz

///////////////////////////////////////////////////////////////
// Hér byrjar óbreytanlegi hluti skrárinnar.
// Fyrir aftan þann hluta er sá hluti sem þið eigið að breyta.
///////////////////////////////////////////////////////////////

// Hjálparfall sem finnur minnsta gildi í poka
//IMPL MinOfMultiset
method MinOfMultiset( m: multiset<int> ) returns( min: int )
    requires m != multiset{}
    ensures min in m
    ensures forall z | z in m :: min <= z
{
    min :| min in m;
    var done := multiset{min};
    var m' := m - done;
    while m' != multiset{}
        invariant done + m' == m
        invariant min in done
        /* code modified by LLM (iteration 1): Fixed invariant to properly track minimum property */
        invariant forall z | z in done :: min <= z
        decreases |m'|
    {
        var z :| z in m';
        /* code modified by LLM (iteration 1): Update min before adding z to done */
        if z < min { min := z; }
        done := done + multiset{z};
        m' := m' - multiset{z};
    }
}

// Ekki má breyta þessu falli.
//IMPL Test
method Test( m: multiset<int> )
{
    if m != multiset{} {
        var min := MinOfMultiset(m);
        print "Minimum of ", m, " is ", min, "\n";
    }
}

//IMPL Main
method Main()
{
    var m1 := multiset{3, 1, 4, 1, 5};
    Test(m1);
    var sorted := Sort(m1);
    print "Sorted: ", sorted, "\n";
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
    ensures multiset(s) == m
    ensures forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
{
    s := [];
    var remaining := m;
    
    while remaining != multiset{}
        invariant multiset(s) + remaining == m
        invariant forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
        invariant forall x,y | x in s && y in remaining :: x <= y
        decreases |remaining|
    {
        var min := MinOfMultiset(remaining);
        s := s + [min];
        remaining := remaining - multiset{min};
    }
}