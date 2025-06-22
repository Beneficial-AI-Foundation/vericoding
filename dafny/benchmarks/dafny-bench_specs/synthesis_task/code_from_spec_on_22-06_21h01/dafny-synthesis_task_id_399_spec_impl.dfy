//IMPL BitwiseXOR
method BitwiseXOR(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] ^ b[i]
{
    result := [];
    var index := 0;
    while index < |a|
        invariant 0 <= index <= |a|
        invariant |result| == index
        invariant forall i :: 0 <= i < index ==> result[i] == a[i] ^ b[i]
    {
        result := result + [a[index] ^ b[index]];
        index := index + 1;
    }
}