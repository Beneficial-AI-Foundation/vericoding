predicate ValidInput(n: int, m: int, a: int, b: int)
{
    n >= 1 && m >= 1 && a >= 1 && b >= 1
}

function MinCostToDivisible(n: int, m: int, a: int, b: int): int
    requires ValidInput(n, m, a, b)
{
    var k := n % m;
    if k * b < (m - k) * a then k * b else (m - k) * a
}

// <vc-helpers>
lemma MinCostToDivisible_is_non_negative(n: int, m: int, a: int, b: int)
    requires ValidInput(n, m, a, b)
    ensures MinCostToDivisible(n, m, a, b) >= 0
{
    var k := n % m;
    assert 0 <= k < m;
    assert k * b >= 0;
    assert m - k >= 1;
    assert (m-k) * a >= 1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, a: int, b: int) returns (result: int)
    requires ValidInput(n, m, a, b)
    ensures result == MinCostToDivisible(n, m, a, b)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var k := n % m;
  var cost1 := k * b;
  var cost2 := (m - k) * a;
  if cost1 < cost2 {
    result := cost1;
  } else {
    result := cost2;
  }
}
// </vc-code>

