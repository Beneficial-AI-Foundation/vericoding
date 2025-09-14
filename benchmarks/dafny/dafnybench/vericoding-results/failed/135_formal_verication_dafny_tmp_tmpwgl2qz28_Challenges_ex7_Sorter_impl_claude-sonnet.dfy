// see pdf 'ex6 & 7 documentation' for excercise question


datatype Bases = A | C | G | T

//swaps two sequence indexes
method Exchanger(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
{
  assume{:axiom} false;
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
lemma BelowTransitive(x: Bases, y: Bases, z: Bases)
    requires below(x, y) && below(y, z)
    ensures below(x, z)
{
}

lemma BelowReflexive(x: Bases)
    ensures below(x, x)
{
}

lemma BelowTotal(x: Bases, y: Bases)
    ensures below(x, y) || below(y, x)
{
}

lemma BorderedSlice(s: seq<Bases>, i: nat, j: nat)
    requires bordered(s)
    requires 0 <= i <= j <= |s|
    ensures bordered(s[i..j])
{
}

lemma BorderedConcat(s1: seq<Bases>, s2: seq<Bases>)
    requires bordered(s1) && bordered(s2)
    requires |s1| == 0 || |s2| == 0 || below(s1[|s1|-1], s2[0])
    ensures bordered(s1 + s2)
{
}

lemma MultisetConcat(s1: seq<Bases>, s2: seq<Bases>)
    ensures multiset(s1 + s2) == multiset(s1) + multiset(s2)
{
}
// </vc-helpers>

// <vc-spec>
method Sorter(bases: seq<Bases>) returns (sobases:seq<Bases>)
requires 0 < |bases|
ensures |sobases| == |bases|
ensures bordered(sobases)
ensures multiset(bases) == multiset(sobases);
// </vc-spec>
// <vc-code>
{
    sobases := bases;
    var i := 0;
    
    while i < |sobases|
        invariant 0 <= i <= |sobases|
        invariant |sobases| == |bases|
        invariant multiset(sobases) == multiset(bases)
        invariant bordered(sobases[0..i])
        invariant forall x, y :: 0 <= x < i && i <= y < |sobases| ==> below(sobases[x], sobases[y])
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
// </vc-code>

