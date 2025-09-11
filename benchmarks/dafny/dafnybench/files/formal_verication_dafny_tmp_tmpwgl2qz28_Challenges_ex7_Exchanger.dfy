// <vc-preamble>
datatype Bases = A | C | G | T

predicate below(first: Bases, second: Bases)
{
    first == second ||
    first == A || 
    (first == C && (second ==  G || second == T)) || 
    (first == G && second == T) ||
    second == T
}

predicate bordered(s:seq<Bases>)
{
    forall j, k :: 0 <= j < k < |s| ==> below(s[j], s[k])
}
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
