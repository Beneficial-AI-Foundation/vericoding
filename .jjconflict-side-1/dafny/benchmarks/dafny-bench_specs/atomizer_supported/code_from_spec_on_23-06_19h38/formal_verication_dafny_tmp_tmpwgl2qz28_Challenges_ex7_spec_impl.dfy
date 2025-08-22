// see pdf 'ex6 & 7 documentation' for excercise question

//ATOM 
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
    /* code modified by LLM (iteration 1): Fixed the postcondition logic - t[y] should equal s[x] */
    t := s[x := s[y]][y := s[x]];
}

//idea from Rustan Leino video "Basics of specification and verification: Lecture 3, the Dutch National Flag algorithm"
//modified for 4 elements
//ATOM 

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
//ATOM 

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
    
    /* code modified by LLM (iteration 1): Fixed loop invariant to properly track sorted portion */
    while i < |sobases|
        invariant 0 <= i <= |sobases|
        invariant |sobases| == |bases|
        invariant multiset(sobases) == multiset(bases)
        invariant forall j, k :: 0 <= j < k < i ==> below(sobases[j], sobases[k])
        invariant forall j, k :: 0 <= j < i && i <= k < |sobases| ==> below(sobases[j], sobases[k])
    {
        var minIdx := i;
        var j := i + 1;
        
        /* code modified by LLM (iteration 1): Fixed inner loop invariant to track minimum element correctly */
        while j < |sobases|
            invariant i <= minIdx < |sobases|
            invariant i <= j <= |sobases|
            invariant forall k :: i <= k < j ==> below(sobases[minIdx], sobases[k]) || sobases[minIdx] == sobases[k]
        {
            /* code modified by LLM (iteration 1): Fixed the comparison logic - we want the minimum element */
            if !below(sobases[minIdx], sobases[j]) && sobases[minIdx] != sobases[j] {
                minIdx := j;
            }
            j := j + 1;
        }
        
        if minIdx != i {
            /* code modified by LLM (iteration 1): Use the Exchanger method to maintain correctness */
            sobases := Exchanger(sobases, i, minIdx);
        }
        i := i + 1;
    }
}

//IMPL 
method Testerexchange() {
    var s := [A, C, G, T];
    var t := Exchanger(s, 0, 3);
    assert t == [T, C, G, A];
    
    var s2 := [G, T, A];
    var t2 := Exchanger(s2, 1, 2);
    assert t2 == [G, A, T];
}

//IMPL 
method Testsort() {
    var s := [T, G, C, A];
    var sorted := Sorter(s);
    assert bordered(sorted);
    assert multiset(sorted) == multiset(s);
    
    var s2 := [G, A, T, C, A];
    var sorted2 := Sorter(s2);
    assert bordered(sorted2);
    assert multiset(sorted2) == multiset(s2);
}