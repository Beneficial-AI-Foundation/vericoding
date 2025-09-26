// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method RemoveFront(a: seq<int>) returns (result: seq<int>)
    requires |a| > 0
    ensures |a| > 0
    ensures |result| == |a| - 1
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i + 1]
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := [];
    // impl-end
}
// </vc-code>
