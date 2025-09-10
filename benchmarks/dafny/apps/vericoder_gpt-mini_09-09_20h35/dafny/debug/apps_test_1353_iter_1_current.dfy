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
  if cost1 <= cost2 {
    if cost1 <= cost3 {
      result := cost1;
    } else {
      result := cost3;
    }
  } else {
    if cost2 <= cost3 {
      result := cost2;
    } else {
      result := cost3;
    }
  }
  assert result == OptimalCost(n, m, a, b);
  assert result >= 0;
}
// </vc-code>

