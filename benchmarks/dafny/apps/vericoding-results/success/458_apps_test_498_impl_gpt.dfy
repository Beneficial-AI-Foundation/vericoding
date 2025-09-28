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
lemma DivUpperBound(t: int, d: int, n: int)
  requires d > 0
  requires 0 <= t < d * n
  ensures t / d <= n - 1
{
  var q := t / d;
  var r := t % d;
  assert 0 <= r < d;
  assert t == q * d + r;
  assert q * d + r < n * d; // from 0 <= t < d*n
  assert r >= 0;
  // Prove q < n
  assert !(q >= n) by {
    if q >= n {
      assert q * d >= n * d;
      assert q * d + r >= q * d;
      assert q * d + r >= n * d;
      // contradiction with q * d + r < n * d
    }
  }
  assert q < n;
  assert q <= n - 1;
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
  var t := k - 1;
  var d := 2 * m;

  assert 1 <= k;
  assert 0 <= t;
  assert d > 0;

  lane := t / d + 1;

  var rem := t % d;
  assert 0 <= rem < d;

  desk := rem / 2 + 1;
  side := if rem % 2 == 0 then "L" else "R";

  // Prove lane bounds
  assert k <= 2 * n * m;
  assert t < 2 * n * m;
  assert d * n == 2 * m * n;
  assert 2 * m * n == 2 * n * m;
  assert t < d * n;
  DivUpperBound(t, d, n);
  assert 1 <= lane;
  assert lane <= n;

  // Prove desk bounds
  assert rem < 2 * m;
  DivUpperBound(rem, 2, m);
  assert 1 <= desk;
  assert desk <= m;
}
// </vc-code>

