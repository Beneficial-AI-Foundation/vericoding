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
        invariant min in m
        invariant forall z | z in done :: min <= z
        invariant done + m' == m
        invariant done != multiset{}
    {
        var z :| z in m';
        done := done + multiset{z};
        m' := m' - multiset{z};
        if z < min { 
            min := z; 
        }
    }
}

//ATOM Test
method Test()
{
    var m1 := multiset{5, 2, 8, 1, 9};
    var min1 := MinOfMultiset(m1);
    assert min1 == 1;
    
    var m2 := multiset{3};
    var min2 := MinOfMultiset(m2);
    assert min2 == 3;
}

//ATOM Main
method Main()
{
    Test();
    print "All tests passed!\n";
}

///////////////////////////////////////////////////////////////
// Hér lýkur óbreytanlega hluta skrárinnar.
// Hér fyrir aftan er sá hluti sem þið eigið að breyta til að
// útfæra afbrigði af selection sort.
///////////////////////////////////////////////////////////////

// Selection sort sem raðar poka í runu.
// Klárið að forrita þetta fall.
//ATOM Sort
method Sort(m: multiset<int>) returns (result: seq<int>)
    ensures multiset(result) == m
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
{
    result := [];
    var remaining := m;
    
    while remaining != multiset{}
        invariant multiset(result) + remaining == m
        invariant forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
        invariant forall i :: 0 <= i < |result| ==> forall x :: x in remaining ==> result[i] <= x
    {
        var min := MinOfMultiset(remaining);
        result := result + [min];
        remaining := remaining - multiset{min};
    }
}