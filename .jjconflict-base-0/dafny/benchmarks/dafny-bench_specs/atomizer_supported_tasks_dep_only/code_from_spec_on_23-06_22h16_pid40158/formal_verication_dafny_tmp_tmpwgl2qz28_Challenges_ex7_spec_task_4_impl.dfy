// see pdf 'ex6 & 7 documentation' for excercise question

datatype Bases = A | C | G | T

//IMPL swaps two sequence indexes
method Exchanger(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
{
    t := s[x := s[y]][y := s[x]];
}

//idea from Rustan Leino video "Basics of specification and verification: Lecture 3, the Dutch National Flag algorithm"
//modified for 4 elements
predicate below(first: Bases, second: Bases)
{
    first == second ||
    first == A || 
    (first == C && (second ==  G || second == T)) || 
    (first == G && second == T) ||
    second == T
}

//checks if a sequence is in base order
predicate bordered(s:seq<Bases>)
{
    forall j, k :: 0 <= j < k < |s| ==> below(s[j], s[k])
}

//IMPL 
method Sorter(bases: seq<Bases>) returns (sobases:seq<Bases>)
requires 0 < |bases|
ensures |sobases| == |bases|
ensures bordered(sobases)
ensures multiset(bases) == multiset(sobases);
{
    sobases := bases;
    var i := 0;
    while i < |sobases|
        invariant 0 <= i <= |sobases|
        invariant |sobases| == |bases|
        invariant multiset(sobases) == multiset(bases)
        invariant forall j, k :: 0 <= j < k < i ==> below(sobases[j], sobases[k])
        invariant forall j :: 0 <= j < i ==> forall k :: i <= k < |sobases| ==> below(sobases[j], sobases[k])
    {
        var minIndex := i;
        var j := i + 1;
        while j < |sobases|
            invariant i <= minIndex < |sobases|
            invariant i <= j <= |sobases|
            invariant forall k :: i <= k < j ==> below(sobases[minIndex], sobases[k])
        {
            if !below(sobases[minIndex], sobases[j]) {
                minIndex := j;
            }
            j := j + 1;
        }
        if minIndex != i {
            sobases := Exchanger(sobases, i, minIndex);
        }
        i := i + 1;
    }
}

//IMPL 
method Testsort() {
    var test1 := [T, G, C, A];
    var result1 := Sorter(test1);
    assert result1 == [A, C, G, T];
    
    var test2 := [A];
    var result2 := Sorter(test2);
    assert result2 == [A];
    
    var test3 := [G, G, A, T];
    var result3 := Sorter(test3);
    assert bordered(result3);
}