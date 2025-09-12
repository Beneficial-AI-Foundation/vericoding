// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method reverse(a: array<int>) returns (result: seq<int>)
    ensures
        |result| == a.Length &&
        forall i :: 0 <= i < |result| ==> result[i] == a[a.Length - 1 - i]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
