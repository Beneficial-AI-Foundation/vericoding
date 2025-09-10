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
function method min(x: int, y: int): int
{
  if x <= y then x else y
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
  var s := n * a;
  var p := ((n + m - 1) / m) * b;
  var q := (n / m) * b + (n % m) * a;

  assert s >= 0;
  assert (n + m - 1) / m >= 0;
  assert p >= 0;
  assert n / m >= 0 && 0 <= n % m;
  assert q >= 0;

  result := min(s, min(p, q));
}
// </vc-code>

