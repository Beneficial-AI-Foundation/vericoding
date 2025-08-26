// The `Sorter` method must return a sequence with the same length, same multiset of elements, and be properly sorted

// I'll implement a simple insertion sort algorithm:

// see pdf 'ex6 & 7 documentation' for excercise question


datatype Bases = A | C | G | T

//swaps two sequence indexes
// <vc-spec>
method Exchanger(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
{
    t := s;
    t := t[ x := s[y]];
    t := t[ y := s[x] ];
    return t;
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

// <vc-helpers>
lemma BelowTransitive(a: Bases, b: Bases, c: Bases)
ensures below(a, b) && below(b, c) ==> below(a, c)
{
    // Proof by cases - Dafny can verify this automatically
}

lemma BelowReflexive(a: Bases)
ensures below(a, a)
{
    // Follows from definition
}

lemma BorderedExtension(s: seq<Bases>, i: int)
requires 0 <= i < |s|
requires forall j, k :: 0 <= j < k < i ==> below(s[j], s[k])
requires forall j :: 0 <= j < i ==> below(s[j], s[i])
ensures forall j, k :: 0 <= j < k <= i ==> below(s[j], s[k])
{
    // This lemma helps prove that extending a sorted prefix preserves sortedness
}

lemma InsertionSortInvariant(s: seq<Bases>, j: int, i: int, originalElement: Bases)
requires 0 <= j <= i < |s|
requires forall x, y :: 0 <= x < y < j ==> below(s[x], s[y])
requires forall x, y :: j < x < y <= i ==> below(s[x], s[y])
requires j < i ==> s[j] == originalElement
requires j > 0 ==> below(s[j-1], s[j])
ensures forall x :: 0 <= x <= i ==> (x < j ==> below(s[x], s[j])) && (x > j ==> below(s[j], s[x]))
{
    // Helper lemma for insertion sort correctness
}
// </vc-helpers>

method Sorter(bases: seq<Bases>) returns (sobases:seq<Bases>)
requires 0 < |bases|
ensures |sobases| == |bases|
ensures bordered(sobases)
ensures multiset(bases) == multiset(sobases)
// </vc-spec>
// <vc-code>
{
    sobases := bases;
    var i := 1;
    
    while i < |sobases|
        invariant 1 <= i <= |sobases|
        invariant |sobases| == |bases|
        invariant multiset(sobases) == multiset(bases)
        invariant forall j, k :: 0 <= j < k < i ==> below(sobases[j], sobases[k])
    {
        var j := i;
        
        while j > 0 && !below(sobases[j-1], sobases[j])
            invariant 0 <= j <= i
            invariant |sobases| == |bases|
            invariant multiset(sobases) == multiset(bases)
            invariant forall x, y :: 0 <= x < y < j ==> below(sobases[x], sobases[y])
            invariant forall x, y :: j < x < y < i ==> below(sobases[x], sobases[y])
            invariant forall x :: j < x <= i ==> below(sobases[j], sobases[x])
        {
            sobases := Exchanger(sobases, j-1, j);
            j := j - 1;
        }
        
        // After the inner loop, j is the correct position and the element is properly placed
        assert j == 0 || below(sobases[j-1], sobases[j]);
        assert forall x :: 0 <= x < j ==> below(sobases[x], sobases[j]);
        assert forall x :: j < x <= i ==> below(sobases[j], sobases[x]);
        
        // Now we can prove the extended sorted property
        assert forall x :: 0 <= x <= i ==> below(sobases[x], sobases[i]) || x == i;
        assert forall x :: 0 <= x < i ==> below(sobases[x], sobases[i]);
        
        BorderedExtension(sobases, i);
        
        i := i + 1;
    }
}
// </vc-code>