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
function SeqToMultiset(s: seq<int>): multiset<int>
    decreases s
{
    if |s| == 0 then multiset{}
    else multiset{s[0]} + SeqToMultiset(s[1..])
}

lemma LemmaSortedSeqProperty(s: seq<int>)
    requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
    ensures forall i,j | 0 <= i <= j < |s| :: s[i] <= s[j]
{
}

lemma LemmaConcatSortedSeqs(a: seq<int>, b: seq<int>, pivot: int)
    requires forall p,q | 0 <= p < q < |a| :: a[p] <= a[q]
    requires forall p,q | 0 <= p < q < |b| :: b[p] <= b[q]
    requires |a| == 0 || forall x | x in multiset(a) :: x <= pivot
    requires |b| == 0 || forall y | y in multiset(b) :: pivot <= y
    ensures forall p,q | 0 <= p < q < |a| + |b| + 1 :: (a + [pivot] + b)[p] <= (a + [pivot] + b)[q]
{
}

lemma LemmaMultisetSubtraction(m: multiset<int>, min: int)
    requires min in m
    ensures m == multiset{min} + (m - multiset{min})
{
}

lemma LemmaPartitionProperty(tail: seq<int>, left: seq<int>, right: seq<int>, min: int, i: int)
    requires |left| + |right| == i
    requires multiset(left) + multiset(right) == multiset(tail[0..i])
    requires forall x | x in multiset(left) :: x <= min
    requires forall y | y in multiset(right) :: min <= y
    requires i < |tail|
    ensures tail[i] <= min ==> multiset(left + [tail[i]]) + multiset(right) == multiset(tail[0..i+1])
    ensures tail[i] > min ==> multiset(left) + multiset(right + [tail[i]]) == multiset(tail[0..i+1])
{
}

lemma LemmaTailSorted(tail: seq<int>)
    requires forall p,q | 0 <= p < q < |tail| :: tail[p] <= tail[q]
    ensures |tail| > 0 ==> forall x | x in multiset(tail) :: tail[0] <= x
{
}

lemma LemmaConcatMultiset(a: seq<int>, b: seq<int>)
    ensures multiset(a + b) == multiset(a) + multiset(b)
{
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
    if m == multiset{} {
        s := [];
    } else {
        var min := MinOfMultiset(m);
        var remaining := m - multiset{min};
        LemmaMultisetSubtraction(m, min);
        var tail : seq<int> := Sort(remaining);
        
        var left : seq<int> := [];
        var right : seq<int> := [];
        
        var i := 0;
        while i < |tail|
            invariant 0 <= i <= |tail|
            invariant |left| + |right| == i
            invariant multiset(left) + multiset(right) == multiset(tail[0..i])
            invariant forall x | x in multiset(left) :: x <= min
            invariant forall y | y in multiset(right) :: min <= y
        {
            if tail[i] <= min {
                left := left + [tail[i]];
            } else {
                right := right + [tail[i]];
            }
            i := i + 1;
        }
        
        LemmaConcatMultiset(left, [min]);
        LemmaConcatMultiset(left + [min], right);
        assert multiset(left + [min] + right) == multiset(left) + multiset([min]) + multiset(right);
        assert multiset(left) + multiset(right) == multiset(tail);
        assert multiset(tail) == remaining;
        assert multiset(left + [min] + right) == remaining + multiset{min} == m;
        
        s := left + [min] + right;
        LemmaConcatSortedSeqs(left, right, min);
    }
}
// </vc-code>

