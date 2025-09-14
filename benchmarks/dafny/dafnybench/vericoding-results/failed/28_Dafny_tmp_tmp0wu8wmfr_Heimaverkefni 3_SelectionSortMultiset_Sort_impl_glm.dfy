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

// </vc-helpers>

// <vc-spec>
method Sort( m: multiset<int> ) returns ( s: seq<int> )
    // Setjið viðeigandi ensures klausur hér
    ensures multiset(s) == m;
    ensures forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
// </vc-spec>
// <vc-code>
{
    var result := [];
    var current := m;
    while |current| > 0
        invariant multiset(result) + current == m
        invariant forall p,q :: 0 <= p < q < |result| ==> result[p] <= result[q]
        invariant |result| == 0 || forall j :: j in current ==> result[|result|-1] <= j
    {
        var min := MinOfMultiset(current);
        result := result + [min];
        current := current - multiset{min};
    }
    return result;
}
// </vc-code>

