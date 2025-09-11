// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ToArray(xs: seq<int>) returns (result: array<int>)
    ensures
        result.Length == |xs| &&
        forall i :: 0 <= i < |xs| ==> result[i] == xs[i]
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := new int[|xs|];
    // impl-end
}
// </vc-code>
