predicate ValidInput(n: int, m: int, k: int)
{
    1 <= n <= 10000 && 1 <= m <= 10000 && 1 <= k <= 2 * n * m
}

predicate ValidOutput(n: int, m: int, lane: int, desk: int, side: string)
{
    1 <= lane <= n && 1 <= desk <= m && (side == "L" || side == "R")
}

predicate CorrectSolution(n: int, m: int, k: int, lane: int, desk: int, side: string)
    requires ValidInput(n, m, k)
{
    lane == (k - 1) / (2 * m) + 1 &&
    desk == (k - 1) % (2 * m) / 2 + 1 &&
    (side == "L" <==> (k - 1) % (2 * m) % 2 == 0)
}

// <vc-helpers>
lemma ValidOutputLemma(n: int, m: int, k: int)
    requires ValidInput(n, m, k)
    ensures 1 <= (k - 1) / (2 * m) + 1 <= n
    ensures 1 <= (k - 1) % (2 * m) / 2 + 1 <= m
{
    // For lower bounds
    assert k >= 1 ==> k - 1 >= 0;
    assert k - 1 >= 0 ==> (k - 1) / (2 * m) >= 0;
    assert k - 1 >= 0 ==> (k - 1) % (2 * m) >= 0;
    
    // For upper bound of lane
    assert k <= 2 * n * m ==> k - 1 < 2 * n * m;
    assert k - 1 < 2 * n * m ==> (k - 1) / (2 * m) < n;
    
    // For upper bound of desk  
    assert (k - 1) % (2 * m) < 2 * m;
    assert (k - 1) % (2 * m) < 2 * m ==> (k - 1) % (2 * m) / 2 < m;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int) returns (lane: int, desk: int, side: string)
    requires ValidInput(n, m, k)
    ensures ValidOutput(n, m, lane, desk, side)
    ensures CorrectSolution(n, m, k, lane, desk, side)
// </vc-spec>
// <vc-code>
{
    ValidOutputLemma(n, m, k);
    
    lane := (k - 1) / (2 * m) + 1;
    desk := (k - 1) % (2 * m) / 2 + 1;
    
    if (k - 1) % (2 * m) % 2 == 0 {
        side := "L";
    } else {
        side := "R";
    }
}
// </vc-code>

