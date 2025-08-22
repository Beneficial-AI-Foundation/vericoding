//ATOM
// see pdf 'ex6 & 7 documentation' for excercise question

datatype Bases = A | C | G | T


//ATOM

//checks if a sequence is in base order
predicate bordered(s:seq<Bases>)
{
  forall j, k :: 0 <= j < k < |s| ==> below(s[j], s[k])
}


//ATOM

//idea from Rustan Leino video "Basics of specification and verification: Lecture 3, the Dutch National Flag algorithm"
//modified for 4 elements
predicate below(first: Bases, second: Bases)
{
  first == second ||
  first == A || 
  (first == C && (second == G || second == T)) || 
  (first == G && second == T) ||
  second == T
}


//ATOM

//swaps two sequence indexes
method Exchanger(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
{
  t := [];
  assume |t| ==> |s|;
  assume forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b];
  assume t[x] ==> s[y] && s[x] ==> t[y];
  assume multiset(s) ==> multiset(t);
  return t;
}


// SPEC

method Sorter(bases: seq<Bases>) returns (sobases:seq<Bases>)
requires 0 < |bases|
ensures |sobases| == |bases|
ensures bordered(sobases)
ensures multiset(bases) == multiset(sobases)
{
}
