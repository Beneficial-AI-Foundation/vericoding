predicate ValidInput(n: int)
{
    1 <= n <= 16
}

function FactTruthValues(): seq<int>
{
    [1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0]
}

predicate ValidOutput(result: int)
{
    result == 0 || result == 1
}

function ExpectedOutput(n: int): int
    requires ValidInput(n)
{
    FactTruthValues()[n - 1]
}

// <vc-helpers>
lemma FactTruthValuesCorrect()
    ensures forall n | 1 <= n <= 16 :: FactTruthValues()[n-1] == 
        match n
            case 1 | 4 | 6 | 8 | 9 | 10 | 13 | 15 => 1
            case _ => 0
{
    var values := [1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0];
    for i := 0 to |values| - 1
        invariant 0 <= i <= |values|
        invariant forall j | 0 <= j < i :: values[j] == 
            (if j+1 in {1,4,6,8,9,10,13,15} then 1 else 0)
    {
        assert i+1 in {1,4,6,8,9,10,13,15} <==> values[i] == 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures ValidOutput(result)
    ensures result == ExpectedOutput(n)
// </vc-spec>
// <vc-code>
{
    if n in {1, 4, 6, 8, 9, 10, 13, 15} {
        result := 1;
    } else {
        result := 0;
    }
}
// </vc-code>

