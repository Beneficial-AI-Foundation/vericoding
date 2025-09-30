predicate ValidInput(input: string)
{
    |input| > 0
}

predicate ValidOutput(result: seq<int>, input: string)
{
    |result| >= 0 &&
    (forall i :: 0 <= i < |result| ==> result[i] >= 1) &&
    (forall i :: 0 <= i < |result| ==> result[i] <= |result|)
}

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: seq<int>)
    requires ValidInput(input)
    ensures ValidOutput(result, input)
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    while i < |input|
        invariant 0 <= i <= |input|
        invariant |result| == i
        invariant forall j :: 0 <= j < |result| ==> result[j] == j + 1
    {
        result := result + [i + 1];
        i := i + 1;
    }
}
// </vc-code>

