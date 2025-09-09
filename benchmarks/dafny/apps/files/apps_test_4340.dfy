Transform an array of integers where odd numbers remain unchanged and even numbers are decremented by 1.

function TransformElement(x: int): int
{
    if x % 2 == 0 then x - 1 else x
}

predicate ValidTransformation(input: seq<int>, output: seq<int>)
{
    |output| == |input| &&
    forall i :: 0 <= i < |input| ==> output[i] == TransformElement(input[i])
}

method solve(a: seq<int>) returns (result: seq<int>)
    ensures ValidTransformation(a, result)
{
    result := seq(|a|, i requires 0 <= i < |a| => TransformElement(a[i]));
}
