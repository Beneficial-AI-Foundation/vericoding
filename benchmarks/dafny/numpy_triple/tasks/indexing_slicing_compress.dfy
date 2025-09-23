// <vc-preamble>
// Helper function to count true values in a boolean sequence
ghost function CountTrue(condition: seq<bool>): nat
{
    if |condition| == 0 then 0
    else (if condition[0] then 1 else 0) + CountTrue(condition[1..])
}

// Helper predicate to check if a mapping preserves order
ghost predicate IsStrictlyIncreasing(mapping: seq<nat>)
{
    forall i, j :: 0 <= i < j < |mapping| ==> mapping[i] < mapping[j]
}

// Helper predicate to check if all mapped indices have true conditions
ghost predicate MappingRespectsConditions(mapping: seq<nat>, condition: seq<bool>)
    requires forall i :: 0 <= i < |mapping| ==> mapping[i] < |condition|
{
    forall i :: 0 <= i < |mapping| ==> condition[mapping[i]]
}

// Helper predicate to check if result elements match original at mapped positions
ghost predicate ResultMatchesOriginal(result: seq<real>, original: seq<real>, mapping: seq<nat>)
    requires |result| == |mapping|
    requires forall i :: 0 <= i < |mapping| ==> mapping[i] < |original|
{
    forall i :: 0 <= i < |result| ==> result[i] == original[mapping[i]]
}

/**
 * Compresses a vector by selecting only elements where the corresponding condition is true.
 * Returns a new vector containing only the selected elements in their original order.
 */
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Compress(condition: seq<bool>, a: seq<real>) returns (result: seq<real>)
    requires |condition| == |a|
    ensures |result| == CountTrue(condition)
    // Result preserves order and corresponds to true conditions via a mapping
    ensures exists mapping: seq<nat> ::
        && |mapping| == |result|
        && (forall i :: 0 <= i < |mapping| ==> mapping[i] < |condition|)
        && MappingRespectsConditions(mapping, condition)
        && ResultMatchesOriginal(result, a, mapping)
        && IsStrictlyIncreasing(mapping)
    // Empty result iff all conditions are false
    ensures (|result| == 0) <==> (forall i :: 0 <= i < |condition| ==> !condition[i])
    // Full result iff all conditions are true
    ensures (|result| == |a|) <==> (forall i :: 0 <= i < |condition| ==> condition[i])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
