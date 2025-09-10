function TransformElement(x: int): int
{
    if x % 2 == 0 then x - 1 else x
}

predicate ValidTransformation(input: seq<int>, output: seq<int>)
{
    |output| == |input| &&
    forall i :: 0 <= i < |input| ==> output[i] == TransformElement(input[i])
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: seq<int>)
    ensures ValidTransformation(a, result)
// </vc-spec>
// <vc-code>
{
    var i := 0;
    var transformed_elements := new int[|a|];
    while i < |a|
        invariant 0 <= i <= |a|
        invariant transformed_elements.Length == |a|
        invariant forall k :: 0 <= k < i ==> transformed_elements[k] == TransformElement(a[k])
    {
        transformed_elements[i] := TransformElement(a[i]);
        i := i + 1;
    }
    var result_seq: seq<int> := [];
    for k := 0 to |a| - 1 {
        result_seq := result_seq + [transformed_elements[k]];
    }
    return result_seq;
}
// </vc-code>

