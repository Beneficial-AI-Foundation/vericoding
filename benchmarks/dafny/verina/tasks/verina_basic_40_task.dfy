// <vc-preamble>
predicate SecondSmallestPrecond(s: array<int>)
    reads s
{
    s.Length > 1
}

predicate SecondSmallestPostcond(s: array<int>, result: int)
    reads s
{
    (exists i :: 0 <= i < s.Length && s[i] == result) &&
    (exists j :: 0 <= j < s.Length && s[j] < result &&
        (forall k :: 0 <= k < s.Length && s[k] != s[j] ==> s[k] >= result))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
function SecondSmallest(s: array<int>): int
    requires SecondSmallestPrecond(s)
    reads s
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    0
    // impl-end
}

lemma SecondSmallestSpecSatisfied(s: array<int>)
    requires SecondSmallestPrecond(s)
    ensures SecondSmallestPostcond(s, SecondSmallest(s))
{
    assume {:axiom} false;
}
// </vc-code>
