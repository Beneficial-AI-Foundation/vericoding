predicate ValidInput(n: int, m: int, a: int, b: int)
{
    n >= 1 && n <= 1000 &&
    m >= 1 && m <= 1000 &&
    a >= 1 && a <= 1000 &&
    b >= 1 && b <= 1000
}

function OptimalCost(n: int, m: int, a: int, b: int): int
    requires ValidInput(n, m, a, b)
{
    min(
        n * a,  // All single tickets
        min(
            ((n + m - 1) / m) * b,  // All multi-ride tickets (with potential waste)
            (n / m) * b + (n % m) * a  // Mixed: multi-ride + single for remainder
        )
    )
}

// <vc-helpers>
function min(x: int, y: int): int
{
  if x <= y then x else y
}

lemma MinNonNeg(x: int, y: int)
  requires x >= 0 && y >= 0
  ensures min(x, y) >= 0
{
  if x <= y {
    assert min(x, y) == x;
    assert x >= 0;
  } else {
    assert min(x, y) == y;
    assert y >= 0;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, a: int, b: int) returns (result: int)
    requires ValidInput(n, m, a, b)
    ensures result >= 0
    ensures result == OptimalCost(n, m, a, b)
// </vc-spec>
// <vc-code>
{
  var cost1 := n * a;
  var cost2 := ((n + m - 1) / m) * b;
  var cost3 := (n / m) * b + (n % m) * a;

  assert cost1 >= 0;
  assert cost2 >= 0;
  assert cost3 >= 0;

  MinNonNeg(cost2, cost3);
  MinNonNeg(cost1, min(cost2, cost3));

  result := min(cost1, min(cost2, cost3));

  assert result == OptimalCost(n, m, a, b);
  assert result >= 0;
}
// </vc-code>

