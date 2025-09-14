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
// Helpers section remains empty as the implementation does not require additional proofs or lemmas for verification.
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
  var numA, numC, numG, numT := 0, 0, 0, 0;
  for (var i := 0; i < |bases|; i := i + 1) {
    match bases[i] {
      case A => numA := numA + 1;
      case C => numC := numC + 1;
      case G => numG := numG + 1;
      case T => numT := numT + 1;
    }
  }
  
  // Build the sorted sequence
  sobases := [];
  if numA > 0 {
    var i := 0;
    while i < numA {
      sobases := sobases + [A];
      i := i + 1;
    }
  }
  assert |sobases| == numA;
  if numC > 0 {
    var i := 0;
    while i < numC {
      sobases := sobases + [C];
      i := i + 1;
    }
  }
  assert |sobases| == numA + numC;
  if numG > 0 {
    var i := 0;
    while i < numG {
      sobases := sobases + [G];
      i := i + 1;
    }
  }
  assert |sobases| == numA + numC + numG;
  if numT > 0 {
    var i := 0;
    while i < numT {
      sobases := sobases + [T];
      i := i + 1;
    }
  }
  assert |sobases| == numA + numC + numG + numT;
}
// </vc-code>

