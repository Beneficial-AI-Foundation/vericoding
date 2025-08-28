// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method BitwiseXOR(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] ^ b[i]
// </vc-spec>
// </vc-spec>

// <vc-code>
method BitwiseXORImpl(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] ^ b[i]
{
    result := seq(|a|, i requires 0 <= i < |a| => a[i] ^ b[i]);
}
// </vc-code>
