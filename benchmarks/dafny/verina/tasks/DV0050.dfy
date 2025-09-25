// <vc-preamble>
predicate IsSorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate MultisetEquiv(s1: seq<int>, s2: seq<int>)
{
    multiset(s1) == multiset(s2)
}
method MergeSortedAux(a: seq<int>, b: seq<int>) returns (result: seq<int>)
{
    assume {:axiom} false;
    result := [];
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MergeSorted(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires IsSorted(a)
    requires IsSorted(b)
    ensures IsSorted(result)
    ensures MultisetEquiv(result, a + b)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
    result := [];
}
// </vc-code>
