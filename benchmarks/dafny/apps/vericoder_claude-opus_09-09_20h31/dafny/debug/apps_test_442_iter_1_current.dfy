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
lemma VerifyH(r: int)
    requires r > 4 && r % 2 == 1
    ensures H(1, (r - 3) / 2) == r
{
    var x := 1;
    var y := (r - 3) / 2;
    calc {
        H(x, y);
        == x * x + 2 * x * y + x + 1;
        == 1 * 1 + 2 * 1 * y + 1 + 1;
        == 1 + 2 * y + 1 + 1;
        == 3 + 2 * y;
        == 3 + 2 * ((r - 3) / 2);
        == 3 + (r - 3);
        == r;
    }
}

lemma PositiveY(r: int)
    requires r > 4 && r % 2 == 1
    ensures (r - 3) / 2 > 0
{
    // r > 4 and r is odd means r >= 5
    // So r - 3 >= 2
    // Therefore (r - 3) / 2 >= 1 > 0
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
        // r > 4 and r is odd
        var x := 1;
        var y := (r - 3) / 2;
        
        PositiveY(r);
        assert y > 0;
        
        VerifyH(r);
        assert H(x, y) == r;
        
        result := [x, y];
    }
}
// </vc-code>

