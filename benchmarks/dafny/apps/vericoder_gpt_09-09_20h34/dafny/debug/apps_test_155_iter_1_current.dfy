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
    // First column traversal
    assert k >= 0;
    assert k + 1 >= 1 && k + 1 <= n;
    result := [k + 1, 1];
  } else {
    var k_remaining := k - n;
    assert m >= 2;
    assert m - 1 > 0;
    assert k_remaining >= 0;
    assert k < n * m;
    assert k_remaining < n * (m - 1);

    var t := k_remaining / (m - 1);
    assert 0 <= t;
    assert t < n; // since k_remaining < n*(m-1) and m-1 > 0
    var r := n - t;
    assert 1 <= r && r <= n;

    var step := k_remaining % (m - 1);
    assert 0 <= step && step < m - 1;

    if r % 2 == 1 {
      // Moving left on odd rows (from perspective of r counting from top)
      // Column in [2..m]
      assert 2 <= m - step && m - step <= m;
      result := [r, m - step];
    } else {
      // Moving right on even rows
      // Column in [2..m]
      assert 2 <= 2 + step && 2 + step <= m;
      result := [r, 2 + step];
    }
  }
}
// </vc-code>

