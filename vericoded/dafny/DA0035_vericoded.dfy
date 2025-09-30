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
lemma ValidRBounds(n: int, m: int, k: int)
    requires ValidInput(n, m, k)
    requires k >= n
    ensures n - (k - n) / (m - 1) >= 1
    ensures n - (k - n) / (m - 1) <= n
{
    var k_remaining := k - n;
    assert k_remaining >= 0;
    assert k_remaining / (m - 1) >= 0;
    assert n - k_remaining / (m - 1) <= n;
    
    assert k < n * m;
    assert k_remaining < n * m - n;
    assert k_remaining < n * (m - 1);
    assert k_remaining / (m - 1) < n;
    assert k_remaining / (m - 1) <= n - 1;
    assert n - k_remaining / (m - 1) >= n - (n - 1);
    assert n - k_remaining / (m - 1) >= 1;
}

lemma ValidPositionBounds(n: int, m: int, k: int, r: int, c: int)
    requires ValidInput(n, m, k)
    requires k >= n
    requires r == n - (k - n) / (m - 1)
    requires r >= 1 && r <= n
    requires if r % 2 == 1 then c == m - (k - n) % (m - 1) else c == 2 + (k - n) % (m - 1)
    ensures c >= 1 && c <= m
{
    var k_remaining := k - n;
    if r % 2 == 1 {
        assert c == m - k_remaining % (m - 1);
        assert k_remaining % (m - 1) >= 0 && k_remaining % (m - 1) < m - 1;
        assert c >= m - (m - 2) && c <= m;
        assert c >= 2 && c <= m;
    } else {
        assert c == 2 + k_remaining % (m - 1);
        assert k_remaining % (m - 1) >= 0 && k_remaining % (m - 1) < m - 1;
        assert c >= 2 && c <= 2 + (m - 2);
        assert c >= 2 && c <= m;
    }
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
    } else {
        var k_remaining := k - n;
        var r := n - k_remaining / (m - 1);
        ValidRBounds(n, m, k);
        assert r >= 1 && r <= n;
        var c: int;
        if r % 2 == 1 {
            c := m - k_remaining % (m - 1);
        } else {
            c := 2 + k_remaining % (m - 1);
        }
        ValidPositionBounds(n, m, k, r, c);
        result := [r, c];
    }
}
// </vc-code>

