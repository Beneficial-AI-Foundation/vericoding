predicate ValidInput(input: seq<(int, int)>)
{
    forall i :: 0 <= i < |input| ==> input[i].0 >= 1 && input[i].1 >= 1
}

function MinMoves(a: int, b: int): int
    requires a >= 1 && b >= 1
{
    if a == b then 0
    else if a < b then
        if (b - a) % 2 == 1 then 1 else 2
    else
        if (a - b) % 2 == 0 then 1 else 2
}

predicate ValidOutput(input: seq<(int, int)>, result: seq<int>)
    requires ValidInput(input)
{
    |result| == |input| &&
    forall i :: 0 <= i < |input| ==> result[i] == MinMoves(input[i].0, input[i].1) &&
    forall i :: 0 <= i < |result| ==> result[i] >= 0
}

// <vc-helpers>
lemma MinMovesLemma(a: int, b: int)
    requires a >= 1 && b >= 1
    ensures MinMoves(a, b) >= 0
{
    // The function always returns 0, 1, or 2, all non-negative
}

lemma MinMovesSymmetry(a: int, b: int)
    requires a >= 1 && b >= 1
    ensures MinMoves(a, b) == MinMoves(b, a)
{
    // The symmetry holds by the definition of MinMoves
    // The function treats both parameters symmetrically
    if a != b {
        if a < b {
            assert (b - a) % 2 == 1 ==> MinMoves(a, b) == 1 && MinMoves(b, a) == if (b - a) % 2 == 0 then 1 else 2;
            assert (b - a) % 2 == 0 ==> MinMoves(a, b) == 2 && MinMoves(b, a) == 1;
        } else {
            assert (a - b) % 2 == 0 ==> MinMoves(a, b) == 1 && MinMoves(b, a) == if (a - b) % 2 == 1 then 1 else 2;
            assert (a - b) % 2 == 1 ==> MinMoves(a, b) == 2 && MinMoves(b, a) == 1;
        }
    }
}

lemma ValidInputPreservesIndices(input: seq<(int, int)>)
    requires ValidInput(input)
    ensures forall i :: 0 <= i < |input| ==> input[i].0 >= 1 && input[i].1 >= 1
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: seq<(int, int)>) returns (result: seq<int>)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    ValidInputPreservesIndices(input);
    while i < |input|
        invariant 0 <= i <= |input|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == MinMoves(input[j].0, input[j].1)
        invariant forall j :: 0 <= j < i ==> result[j] >= 0
    {
        var a := input[i].0;
        var b := input[i].1;
        assert a >= 1 && b >= 1; // From ValidInput
        MinMovesLemma(a, b);
        var moves := MinMoves(a, b);
        result := result + [moves];
        i := i + 1;
    }
}
// </vc-code>

