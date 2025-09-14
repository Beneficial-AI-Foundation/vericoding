// see pdf 'ex6 & 7 documentation' for excercise question


datatype Bases = A | C | G | T

//swaps two sequence indexes

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
lemma SwapMultiset(s: seq<Bases>, x: nat, y: nat)
    requires 0 <= x < y < |s|
    ensures multiset(s) == multiset(s[..x] + [s[y]] + s[x+1..y] + [s[x]] + s[y+1..])
{
    var a := s[..x];
    var u := s[x];
    var b := s[x+1..y];
    var v := s[y];
    var c := s[y+1..];
    assert s == a + [u] + b + [v] + c;
    calc {
        multiset(s);
        == { }
        multiset(a + [u] + b + [v] + c);
        == { }
        multiset(a) + multiset([u] + b + [v] + c);
        == { }
        multiset(a) + multiset([u]) + multiset(b + [v] + c);
        == { }
        multiset(a) + multiset([u]) + multiset(b) + multiset([v] + c);
        == { }
        multiset(a) + multiset([u]) + multiset(b) + multiset([v]) + multiset(c);
        == { }
        multiset(a) + multiset([v]) + multiset(b) + multiset([u]) + multiset(c);
        == { }
        multiset(a + [v] + b + [u] + c);
    }
    assert multiset(a + [v] + b + [u] + c) == multiset(s[..x] + [s[y]] + s[x+1..y] + [s[x]] + s[y+1..]);
}
// </vc-helpers>

// <vc-spec>
method Exchanger(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
// </vc-spec>
// <vc-code>
{
  if x == y {
    t := s;
  } else if x < y {
    t := s[..x] + [s[y]] + s[x+1..y] + [s[x]] + s[y+1..];
    SwapMultiset(s, x, y);
  } else {
    // y < x
    t := s[..y] + [s[x]] + s[y+1..x] + [s[y]] + s[x+1..];
    SwapMultiset(s, y, x);
  }
}
// </vc-code>

