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
    if r <= 4 || r % 2 == 0 then
        result := []
    else
        // r > 4 and r % 2 == 1
        // We need to find x, y > 0 such that H(x, y) == r
        // H(x, y) = x*x + 2*x*y + x + 1
        // From the postcondition, we know that if a solution exists, it is x = 1 and y = (r - 3) / 2
        // Let's verify this solution:
        // H(1, (r-3)/2) = 1*1 + 2*1*((r-3)/2) + 1 + 1
        //               = 1 + (r-3) + 1 + 1
        //               = r - 3 + 3
        //               = r
        // We also need to ensure that y > 0:
        // (r - 3) / 2 > 0  <==> r - 3 > 0 <==> r > 3
        // Since r > 4, we have r > 3, so (r - 3) / 2 will be a positive integer.
        // Therefore, x = 1 and y = (r - 3) / 2 is a valid solution.
        var x := 1;
        var y := (r - 3) / 2;
        result := [x, y];
    
}
// </vc-code>

