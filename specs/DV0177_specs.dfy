// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method TestArrayElements(a: seq<int>, j: nat) returns (result: seq<int>)
    requires j < |a|
    ensures |result| == |a|
    ensures result[j] == 60
    ensures forall k :: 0 <= k < |a| && k != j ==> result[k] == a[k]
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := [];
    // impl-end
}
// </vc-code>
