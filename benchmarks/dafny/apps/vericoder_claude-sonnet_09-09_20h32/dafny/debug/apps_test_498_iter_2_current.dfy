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
lemma LaneInBounds(n: int, m: int, k: int)
    requires ValidInput(n, m, k)
    ensures 1 <= (k - 1) / (2 * m) + 1 <= n
{
    var lane_val := (k - 1) / (2 * m) + 1;
    
    // Show lane_val >= 1
    assert k >= 1;
    assert (k - 1) >= 0;
    assert (k - 1) / (2 * m) >= 0;
    assert lane_val >= 1;
    
    // Show lane_val <= n
    assert k <= 2 * n * m;
    assert (k - 1) <= 2 * n * m - 1;
    
    // Use the fact that for integers a, b with b > 0: a / b <= (a + b - 1) / b
    // and specifically (2 * n * m - 1) / (2 * m) = n - 1/2m which is < n
    calc {
        (k - 1) / (2 * m);
        <= { assert (k - 1) <= 2 * n * m - 1; }
        (2 * n * m - 1) / (2 * m);
        == { assert 2 * n * m - 1 == (2 * m) * (n - 1) + (2 * m - 1); }
        (n - 1) + (2 * m - 1) / (2 * m);
        == { assert (2 * m - 1) / (2 * m) == 0; }
        n - 1;
    }
    
    assert (k - 1) / (2 * m) <= n - 1;
    assert lane_val <= n;
}

lemma DeskInBounds(n: int, m: int, k: int)
    requires ValidInput(n, m, k)
    ensures 1 <= (k - 1) % (2 * m) / 2 + 1 <= m
{
    assert (k - 1) % (2 * m) >= 0;
    assert (k - 1) % (2 * m) < 2 * m;
    assert (k - 1) % (2 * m) / 2 >= 0;
    assert (k - 1) % (2 * m) / 2 < m;
    assert (k - 1) % (2 * m) / 2 + 1 >= 1;
    assert (k - 1) % (2 * m) / 2 + 1 <= m;
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
    lane := (k - 1) / (2 * m) + 1;
    desk := (k - 1) % (2 * m) / 2 + 1;
    
    if (k - 1) % (2 * m) % 2 == 0 {
        side := "L";
    } else {
        side := "R";
    }
    
    LaneInBounds(n, m, k);
    DeskInBounds(n, m, k);
}
// </vc-code>

