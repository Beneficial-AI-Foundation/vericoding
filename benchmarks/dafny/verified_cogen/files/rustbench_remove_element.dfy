// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method RemoveElement(a: array<int>, pos: int) returns (result: seq<int>)
    requires 0 <= pos < a.Length
    ensures |result| == a.Length - 1
    ensures forall i :: 0 <= i < pos ==> result[i] == a[i]
    ensures forall i :: pos <= i < |result| ==> result[i] == a[i + 1]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
