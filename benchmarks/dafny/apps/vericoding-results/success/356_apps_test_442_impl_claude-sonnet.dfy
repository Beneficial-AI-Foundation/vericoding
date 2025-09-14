function H(x: int, y: int): int
{
    x * x + 2 * x * y + x + 1
}

predicate ValidInput(r: int)
{
    r > 0
}

predicate ValidSolution(result: seq<int>, r: int)
{
    if |result| == 0 then
        true
    else
        |result| == 2 && result[0] > 0 && result[1] > 0 && H(result[0], result[1]) == r
}

predicate HasSolution(r: int)
{
    r > 4 && r % 2 == 1
}

// <vc-helpers>
lemma HSolutionLemma(r: int)
    requires r > 4 && r % 2 == 1
    ensures H(1, (r - 3) / 2) == r
{
    var y := (r - 3) / 2;
    assert r % 2 == 1;
    assert (r - 3) % 2 == 0;
    assert 2 * y == r - 3;
    
    calc {
        H(1, y);
        1 * 1 + 2 * 1 * y + 1 + 1;
        1 + 2 * y + 2;
        3 + 2 * y;
        3 + (r - 3);
        r;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(r: int) returns (result: seq<int>)
    requires ValidInput(r)
    ensures ValidSolution(result, r)
    ensures |result| == 0 || |result| == 2
    ensures |result| == 2 ==> result[0] > 0 && result[1] > 0
    ensures |result| == 2 ==> H(result[0], result[1]) == r
    ensures r <= 4 ==> |result| == 0
    ensures r > 4 && r % 2 == 0 ==> |result| == 0
    ensures r > 4 && r % 2 == 1 ==> |result| == 2 && result[0] == 1 && result[1] == (r - 3) / 2
// </vc-spec>
// <vc-code>
{
    if r <= 4 {
        result := [];
    } else if r % 2 == 0 {
        result := [];
    } else {
        var y := (r - 3) / 2;
        HSolutionLemma(r);
        result := [1, y];
    }
}
// </vc-code>

