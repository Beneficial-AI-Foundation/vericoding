// see pdf 'ex6 & 7 documentation' for excercise question


datatype Bases = A | C | G | T

//swaps two sequence indexes

// <vc-helpers>
lemma MultisetSwapLemma(s: seq<Bases>, x: nat, y: nat, t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
requires |t| == |s|
requires forall i :: 0 <= i < |s| ==> 
  (if i == x then t[i] == s[y] 
   else if i == y then t[i] == s[x] 
   else t[i] == s[i])
ensures multiset(s) == multiset(t)
{
  if x == y {
    assert forall i :: 0 <= i < |s| ==> t[i] == s[i];
    assert s == t;
  } else {
    if x < y {
      assert multiset(s) == multiset(s[..x]) + multiset([s[x]]) + multiset(s[x+1..y]) + multiset([s[y]]) + multiset(s[y+1..]) by {
        MultisetDecomposition(s, x, y);
      }
      assert multiset(t) == multiset(t[..x]) + multiset([t[x]]) + multiset(t[x+1..y]) + multiset([t[y]]) + multiset(t[y+1..]) by {
        MultisetDecomposition(t, x, y);
      }
      // Show that corresponding parts are equal
      assert t[..x] == s[..x];
      assert t[x] == s[y];
      assert t[x+1..y] == s[x+1..y];
      assert t[y] == s[x];
      assert t[y+1..] == s[y+1..];
      assert multiset(t) == multiset(s[..x]) + multiset([s[y]]) + multiset(s[x+1..y]) + multiset([s[x]]) + multiset(s[y+1..]);
      assert multiset([s[x]]) + multiset([s[y]]) == multiset([s[y]]) + multiset([s[x]]);
    } else {
      assert y < x;
      assert multiset(s) == multiset(s[..y]) + multiset([s[y]]) + multiset(s[y+1..x]) + multiset([s[x]]) + multiset(s[x+1..]) by {
        MultisetDecomposition(s, y, x);
      }
      assert multiset(t) == multiset(t[..y]) + multiset([t[y]]) + multiset(t[y+1..x]) + multiset([t[x]]) + multiset(t[x+1..]) by {
        MultisetDecomposition(t, y, x);
      }
      // Show that corresponding parts are equal
      assert t[..y] == s[..y];
      assert t[y] == s[x];
      assert t[y+1..x] == s[y+1..x];
      assert t[x] == s[y];
      assert t[x+1..] == s[x+1..];
      assert multiset(t) == multiset(s[..y]) + multiset([s[x]]) + multiset(s[y+1..x]) + multiset([s[y]]) + multiset(s[x+1..]);
      assert multiset([s[y]]) + multiset([s[x]]) == multiset([s[x]]) + multiset([s[y]]);
    }
  }
}

lemma MultisetDecomposition(s: seq<Bases>, x: nat, y: nat)
requires 0 <= x < y < |s|
ensures multiset(s) == multiset(s[..x]) + multiset([s[x]]) + multiset(s[x+1..y]) + multiset([s[y]]) + multiset(s[y+1..])
{
  assert s == s[..x] + [s[x]] + s[x+1..y] + [s[y]] + s[y+1..];
  assert multiset(s) == multiset(s[..x] + [s[x]] + s[x+1..y] + [s[y]] + s[y+1..]);
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
  t := seq(|s|, i requires 0 <= i < |s| => if i == x then s[y] else if i == y then s[x] else s[i]);
  
  MultisetSwapLemma(s, x, y, t);
}
// </vc-code>

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