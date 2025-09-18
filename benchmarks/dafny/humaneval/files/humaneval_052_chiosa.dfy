// <vc-preamble>
// ======= TASK =======
// Given a list of integers and a threshold integer, determine if all numbers 
// in the list are strictly less than the threshold.

// ======= SPEC REQUIREMENTS =======
predicate BelowThreshold(l: seq<int>, t: int)
{
    forall i :: 0 <= i < |l| ==> l[i] < t
}
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method CheckBelowThreshold(l: seq<int>, t: int) returns (result: bool)
    ensures result == BelowThreshold(l, t)
// </vc-spec>
// <vc-code>
{
    result := forall i :: 0 <= i < |l| ==> l[i] < t;
}
// </vc-code>
