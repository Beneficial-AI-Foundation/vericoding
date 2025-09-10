predicate ValidInput(n: int, m: int, k: int) {
    n >= 2 && m >= 2 && n % 2 == 0 && k >= 0 && k < n * m
}

predicate ValidOutput(result: seq<int>, n: int, m: int) {
    |result| == 2 && result[0] >= 1 && result[0] <= n && result[1] >= 1 && result[1] <= m
}

predicate CorrectPosition(result: seq<int>, n: int, m: int, k: int) 
    requires ValidInput(n, m, k)
    requires |result| == 2
{
    if k < n then
        result[0] == k + 1 && result[1] == 1
    else
        var k_remaining := k - n;
        var r := n - k_remaining / (m - 1);
        result[0] == r &&
        (r % 2 == 1 ==> result[1] == m - k_remaining % (m - 1)) &&
        (r % 2 == 0 ==> result[1] == 2 + k_remaining % (m - 1))
}

// <vc-helpers>
lemma ValidOutputHelper(r: int, col: int, n: int, m: int)
    requires n >= 2 && m >= 2
    requires r >= 1 && r <= n
    requires col >= 2 && col <= m
    ensures ValidOutput([r, col], n, m)
{
}

lemma FirstColumnValidOutput(k: int, n: int, m: int)
    requires ValidInput(n, m, k)
    requires k < n
    ensures ValidOutput([k + 1, 1], n, m)
{
}

lemma ZigzagValidOutput(n: int, m: int, k: int, k_remaining: int, r: int, col: int)
    requires ValidInput(n, m, k)
    requires k >= n
    requires k_remaining == k - n
    requires r == n - k_remaining / (m - 1)
    requires k_remaining >= 0
    requires k_remaining / (m - 1) < n
    requires (r % 2 == 1 ==> col == m - k_remaining % (m - 1)) &&
             (r % 2 == 0 ==> col == 2 + k_remaining % (m - 1))
    ensures ValidOutput([r, col], n, m)
{
    assert r >= 1;
    assert r <= n;
    
    if r % 2 == 1 {
        assert col == m - k_remaining % (m - 1);
        assert k_remaining % (m - 1) >= 0;
        assert k_remaining % (m - 1) < m - 1;
        assert col >= m - (m - 2);
        assert col <= m;
        assert col >= 2;
    } else {
        assert col == 2 + k_remaining % (m - 1);
        assert k_remaining % (m - 1) >= 0;
        assert k_remaining % (m - 1) < m - 1;
        assert col >= 2;
        assert col <= 2 + (m - 2);
        assert col <= m;
    }
}

lemma KRemainingBound(n: int, m: int, k: int)
    requires ValidInput(n, m, k)
    requires k >= n
    ensures k - n < (n - 1) * (m - 1) + 1
{
    assert k < n * m;
    assert k - n < n * m - n;
    assert n * m - n == n * (m - 1);
    assert n >= 2;
    assert n * (m - 1) <= (n - 1) * (m - 1) + (m - 1);
    assert (n - 1) * (m - 1) + (m - 1) == (n - 1) * (m - 1) + m - 1;
    assert m >= 2;
    assert m - 1 >= 1;
    assert (n - 1) * (m - 1) + m - 1 <= (n - 1) * (m - 1) + (n - 1) * (m - 1) + 1;
    calc {
        n * (m - 1);
        ==
        (n - 1 + 1) * (m - 1);
        ==
        (n - 1) * (m - 1) + (m - 1);
    }
    assert m - 1 < n;
    assert (n - 1) * (m - 1) + (m - 1) < (n - 1) * (m - 1) + n;
    assert (n - 1) * (m - 1) + n <= (n - 1) * (m - 1) + (n - 1) + 1;
    assert (n - 1) * (m - 1) + (n - 1) + 1 == 2 * (n - 1) * (m - 1) + 1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, m, k)
    ensures ValidOutput(result, n, m)
    ensures CorrectPosition(result, n, m, k)
// </vc-spec>
// <vc-code>
{
    if k < n {
        result := [k + 1, 1];
        FirstColumnValidOutput(k, n, m);
    } else {
        var k_remaining := k - n;
        var r := n - k_remaining / (m - 1);
        var col: int;
        
        if r % 2 == 1 {
            col := m - k_remaining % (m - 1);
        } else {
            col := 2 + k_remaining % (m - 1);
        }
        
        result := [r, col];
        
        assert k_remaining >= 0;
        assert k < n * m;
        KRemainingBound(n, m, k);
        assert k_remaining < (n - 1) * (m - 1) + 1;
        assert k_remaining / (m - 1) < n;
        
        ZigzagValidOutput(n, m, k, k_remaining, r, col);
    }
}
// </vc-code>

