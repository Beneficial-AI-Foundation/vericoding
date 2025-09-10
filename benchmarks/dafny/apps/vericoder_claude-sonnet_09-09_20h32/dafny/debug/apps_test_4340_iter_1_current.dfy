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
lemma TransformElementPreservesLength(a: seq<int>)
    ensures |seq(|a|, i requires 0 <= i < |a| => TransformElement(a[i]))| == |a|
{
}

lemma TransformElementCorrectness(a: seq<int>, i: int)
    requires 0 <= i < |a|
    ensures (seq(|a|, j requires 0 <= j < |a| => TransformElement(a[j])))[i] == TransformElement(a[i])
{
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: seq<int>)
    ensures ValidTransformation(a, result)
// </vc-spec>
// <vc-code>
{
    result := seq(|a|, i requires 0 <= i < |a| => TransformElement(a[i]));
}
// </vc-code>

