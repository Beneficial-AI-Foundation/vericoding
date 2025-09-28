// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ArraySum(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] + b[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added bounds check for sequence constructor */
    result := seq(|a|, i requires 0 <= i < |a| => a[i] + b[i]);
}
// </vc-code>
