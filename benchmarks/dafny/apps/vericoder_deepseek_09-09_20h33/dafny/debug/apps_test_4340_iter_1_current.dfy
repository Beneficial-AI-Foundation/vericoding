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
lemma TransformElementLemma(x: int)
    ensures TransformElement(x) == if x % 2 == 0 then x - 1 else x
{
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: seq<int>)
    ensures ValidTransformation(a, result)
// </vc-spec>
// <vc-code>
{
    result := [];
    var index := 0;
    while index < |a|
        invariant |result| == index
        invariant forall i :: 0 <= i < index ==> result[i] == TransformElement(a[i])
    {
        var transformed := if a[index] % 2 == 0 then a[index] - 1 else a[index];
        result := result + [transformed];
        index := index + 1;
    }
}
// </vc-code>

