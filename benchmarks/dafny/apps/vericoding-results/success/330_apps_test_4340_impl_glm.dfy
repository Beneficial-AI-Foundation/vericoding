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
    var resultArr := new int[|a|];
    for i := 0 to |a|
        invariant 0 <= i <= |a|
        invariant forall j :: 0 <= j < i ==> resultArr[j] == TransformElement(a[j])
    {
        resultArr[i] := TransformElement(a[i]);
    }
    result := resultArr[..];
}
// </vc-code>

