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
predicate below_predicate(first: Bases, second: Bases)
{
    first == second ||
    first == A || 
    (first == C && (second ==  G || second == T)) || 
    (first == G && second == T) ||
    second == T
}

predicate bordered_predicate(s:seq<Bases>)
{
    forall j, k :: 0 <= j < k < |s| ==> below_predicate(s[j], s[k])
}

lemma Exchanger_properties(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
{
    t := s[x := s[y]][y := s[x]];
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
   var N := |bases|;
   if N <= 1 {
     sobases := bases;
     return;
   }

   var a := bases;
   for i := 0 to N - 2
     invariant 0 <= i < N
     invariant |a| == N
     invariant multiset(a) == multiset(bases)
     invariant forall j, k :: 0 <= j < k < i ==> bordered_predicate(a[j..k+1])
     invariant forall j :: 0 <= j < i ==> (forall k :: i <= k < N ==> below_predicate(a[j], a[k]))
   {
     var minIdx := i;
     for j := i + 1 to N - 1
       invariant i <= minIdx < N
       invariant i <= j <= N
       invariant forall k :: i <= k < j ==> below_predicate(a[minIdx], a[k])
       invariant forall k :: i <= k < j ==> (below_predicate(a[minIdx], a[k]) || k == minIdx)
     {
       if below_predicate(a[j], a[minIdx]) {
         minIdx := j;
       }
     }
     if minIdx != i {
       a := Exchanger_properties(a, i, minIdx);
     }
   }
   sobases := a;
   assert bordered_predicate(sobases); 
}
// </vc-code>

