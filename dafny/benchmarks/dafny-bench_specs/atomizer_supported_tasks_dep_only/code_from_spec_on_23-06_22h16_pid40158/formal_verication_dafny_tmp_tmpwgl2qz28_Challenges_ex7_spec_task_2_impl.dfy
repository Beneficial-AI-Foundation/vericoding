// see pdf 'ex6 & 7 documentation' for excercise question

//ATOM Bases
datatype Bases = A | C | G | T

//IMPL 
//swaps two sequence indexes
method Exchanger(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && t[y] == s[x]
ensures multiset(s) == multiset(t)
{
    /* code modified by LLM (iteration 1): Fixed sequence update order to correctly swap elements */
    if x == y {
        t := s;
    } else {
        t := s[x := s[y]][y := s[x]];
    }
}

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
    while i < |sobases|
        invariant 0 <= i <= |sobases|
        invariant |sobases| == |bases|
        invariant multiset(sobases) == multiset(bases)
        /* code modified by LLM (iteration 2): Fixed invariant to correctly express that elements 0..i-1 are sorted */
        invariant forall j, k :: 0 <= j < k < i ==> below(sobases[j], sobases[k])
    {
        var j := i;
        while j > 0 && !below(sobases[j-1], sobases[j])
            invariant 0 <= j <= i
            invariant |sobases| == |bases|
            invariant multiset(sobases) == multiset(bases)
            /* code modified by LLM (iteration 2): Added invariant that prefix remains sorted */
            invariant forall p, q :: 0 <= p < q < j ==> below(sobases[p], sobases[q])
            /* code modified by LLM (iteration 2): Added invariant that suffix remains sorted */
            invariant forall p, q :: j < p < q <= i ==> below(sobases[p], sobases[q])
            /* code modified by LLM (iteration 2): Added invariant for ordering between prefix and current element */
            invariant forall p :: 0 <= p < j ==> below(sobases[p], sobases[j])
            /* code modified by LLM (iteration 2): Added invariant for ordering between current element and suffix */
            invariant forall q :: j < q <= i ==> below(sobases[j], sobases[q])
            decreases j
        {
            /* code modified by LLM (iteration 2): Used inline swap to maintain multiset property */
            sobases := sobases[j-1 := sobases[j]][j := sobases[j-1]];
            j := j - 1;
        }
        i := i + 1;
    }
}

//ATOM Testerexchange

//ATOM Testsort