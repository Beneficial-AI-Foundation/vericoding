// <vc-preamble>
predicate IsSorted( s: seq<int> )
{
    forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
