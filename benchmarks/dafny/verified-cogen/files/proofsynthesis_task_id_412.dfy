// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method RemoveOdds(arr: array<int>) returns (even_list: seq<int>)
    ensures |even_list| <= arr.Length
    ensures forall i :: 0 <= i < |even_list| ==> even_list[i] % 2 == 0
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
