

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method BitwiseXOR(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] ^ b[i]
// </vc-spec>
// <vc-code>
{
    var newResult: array<bv32> := new bv32[|a|];
    for i := 0 to |a|
        invariant 0 <= i <= |a|
        invariant forall k :: 0 <= k < i ==> newResult[k] == a[k] ^ b[k]
    {
        if i < |a| {
            newResult[i] := a[i] ^ b[i];
        }
    }
    return newResult[..];
}
// </vc-code>

