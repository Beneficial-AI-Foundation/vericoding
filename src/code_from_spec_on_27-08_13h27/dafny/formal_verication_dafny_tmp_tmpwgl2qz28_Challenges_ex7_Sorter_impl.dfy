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
// Helper lemma to prove properties about below relation
lemma BelowTransitive(a: Bases, b: Bases, c: Bases)
  ensures below(a, b) && below(b, c) ==> below(a, c)
{
  if below(a, b) && below(b, c) {
    if a == b || b == c {
      // Trivial cases where equality holds
    } else if a == A {
      // A is below everything
    } else if c == T {
      // T is above everything
    } else if a == C && b == G && c == T {
      // C < G < T
    } else if a == C && b == C && c == G {
      // C < G
    } else if a == C && b == C && c == T {
      // C < T
    } else if a == G && b == G && c == T {
      // G < T
    }
  }
}

// Helper lemma to maintain multiset property after exchange
lemma MultisetPreservedAfterExchange(s: seq<Bases>, t: seq<Bases>, x: nat, y: nat)
  requires 0 < |s| && x < |s| && y < |s|
  requires |t| == |s|
  requires forall b: nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
  requires t[x] == s[y] && t[y] == s[x]
  ensures multiset(s) == multiset(t)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Sorter(bases: seq<Bases>) returns (sobases:seq<Bases>)
requires 0 < |bases|
ensures |sobases| == |bases|
ensures bordered(sobases)
ensures multiset(bases) == multiset(sobases);
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var sorted := bases;
  var n := |bases|;
  
  // Bubble sort-like approach using Exchanger to swap elements
  for i := 0 to n
    invariant 0 <= i <= n
    invariant |sorted| == |bases|
    invariant multiset(sorted) == multiset(bases)
    invariant forall j, k :: 0 <= j < k < i ==> below(sorted[j], sorted[k])
  {
    for j := 0 to n - i - 1
      invariant 0 <= j <= n - i - 1
      invariant |sorted| == |bases|
      invariant multiset(sorted) == multiset(bases)
      invariant forall a, b :: 0 <= a < b < i ==> below(sorted[a], sorted[b])
      invariant forall a, b :: i <= a < b < j + i ==> below(sorted[a], sorted[b])
      invariant forall a, b :: i <= a < j + i <= b < n ==> below(sorted[a], sorted[b])
    {
      if j + i + 1 < n && !below(sorted[j + i], sorted[j + i + 1]) {
        var newSorted := Exchanger(sorted, j + i, j + i + 1);
        MultisetPreservedAfterExchange(sorted, newSorted, j + i, j + i + 1);
        sorted := newSorted;
        assert multiset(sorted) == multiset(bases);
      }
    }
  }
  
  sobases := sorted;
  return sobases;
}
// </vc-code>
