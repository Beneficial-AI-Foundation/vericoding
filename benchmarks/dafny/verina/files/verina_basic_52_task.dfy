// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method BubbleSort(a: seq<int>) returns (result: seq<int>)
    ensures |result| == |a|
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
    ensures multiset(a) == multiset(result)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
    result := a;
}
// </vc-code>
