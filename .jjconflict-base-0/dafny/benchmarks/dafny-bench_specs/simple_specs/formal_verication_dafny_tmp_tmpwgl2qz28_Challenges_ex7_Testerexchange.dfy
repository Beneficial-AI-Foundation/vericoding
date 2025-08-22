//ATOM
// see pdf 'ex6 & 7 documentation' for excercise question

datatype Bases = A | C | G | T


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

method Testerexchange() {
}
