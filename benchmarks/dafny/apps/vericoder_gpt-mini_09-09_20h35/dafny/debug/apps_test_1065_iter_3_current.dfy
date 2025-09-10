predicate ValidInput(n: int, k: int, M: int, D: int) {
    2 <= n && 2 <= k <= n && 1 <= M <= n && 1 <= D <= n && M * D * k >= n
}

function CandiesUsed(x: int, d: int, k: int): int {
    x * ((d - 1) * k + 1)
}

predicate ValidDistribution(x: int, d: int, n: int, k: int, M: int, D: int) {
    1 <= x <= M && 1 <= d <= D && CandiesUsed(x, d, k) <= n
}

function Person1Candies(x: int, d: int): int {
    x * d
}

// <vc-helpers>
lemma DivMulLe(n: int, denom: int)
    requires denom > 0
    ensures (n / denom) * denom <= n
{
    // n == (n/denom)*denom + n%denom and n%denom >= 0
    assert n == (n / denom) * denom + n % denom;
    assert n % denom >= 0;
    assert (n / denom) * denom <= n;
}

lemma DivBounds(n: int, denom: int)
    requires denom > 0
    ensures (n / denom) * denom <= n
    ensures n < (n / denom + 1) * denom
{
    // from division remainder properties
    assert n == (n / denom) * denom + n % denom;
    assert n % denom < denom;
    assert (n / denom) * denom <= n;
    assert n < (n / denom) * denom + denom;
    assert n < (n / denom + 1) * denom;
}

lemma MulLeMonotone(a: int, b: int, c: int)
    requires a <= b
    requires c >= 0
    ensures a * c <= b * c
{
    // (b - a) * c >= 0 implies b*c - a*c >= 0
    assert (b - a) * c >= 0;
    assert b * c - a * c == (b - a) * c;
    assert b * c - a * c >= 0;
    assert a * c <= b * c;
}

lemma MulLe2(a: int, b: int, c: int, d: int)
    requires 0 <= a <= c
    requires 0 <= b <= d
    ensures a * b <= c * d
{
    // a*b <= c*b (since a <= c and b >= 0)
    MulLeMonotone(a, c, b);
    // c*b <= c*d (since b <= d and c >= 0)
    MulLeMonotone(b, d, c);
    // combine: a*b <= c*b <= c*d
    assert a * b <= c * d;
}

lemma MulLeImpDiv(n: int, denom: int, x: int)
    requires denom > 0
    requires x * denom <= n
    ensures x <= n / denom
{
    var q := n / denom;
    // using DivBounds: q*denom <= n < (q+1)*denom
    DivBounds(n, denom);
    // if x > q then x*denom >= (q+1)*denom > n, contradiction
    if x > q {
        assert x >= q + 1;
        assert x * denom >= (q + 1) * denom;
        assert (q + 1) * denom > n; // from DivBounds
        calc { x * denom >= (q + 1) * denom; (q + 1) * denom > n; }
    }
    // therefore x <= q
}

lemma CandiesUsedForChosenX(n: int, k: int, M: int, D: int, d: int, raw: int, mx: int)
    requires 1 <= d <= D
    requires 1 <= k
    requires 1 <= M
    requires raw == n / ((d - 1) * k + 1)
    requires mx == (if raw > M then M else raw)
    requires mx >= 1
    ensures CandiesUsed(mx, d, k) <= n
{
    var denom := (d - 1) * k + 1;
    assert denom > 0;
    if mx == raw {
        // raw * denom <= n
        DivMulLe(n, denom);
        assert raw * denom <= n;
        assert CandiesUsed(mx, d, k) == mx * denom;
        assert mx * denom <= n;
    } else {
        // mx == M and M <= raw
        assert raw > M;
        assert M <= raw;
        // M*denom <= raw*denom
        MulLeMonotone(M, raw, denom);
        assert M * denom <= raw * denom;
        DivMulLe(n, denom);
        assert raw * denom <= n;
        assert M * denom <= n;
        assert CandiesUsed(mx, d, k) == mx * denom;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, M: int, D: int) returns (result: int)
    requires ValidInput(n, k, M, D)
    ensures result >= 0
    ensures result <= M * D
    ensures forall x: int, d: int :: ValidDistribution(x, d, n, k, M, D) ==> Person1Candies(x, d) <= result
    ensures exists x: int, d: int :: ValidDistribution(x, d, n, k, M, D) && Person1Candies(x, d) == result
// </vc-spec>
// <vc-code>
{
  // Initialize with a known valid distribution (1,1)
  var best := 1;
  var best_x := 1;
  var best_d := 1;

  var d := 1;
  while d <= D
    decreases D - d + 1
    invariant 1 <= best <= M * D
    invariant 1 <= best_x <= M
    invariant 1 <= best_d <= D
    invariant best == best_x * best_d
    invariant ValidDistribution(best_x, best_d, n, k, M, D)
  {
    var denom := (d - 1) * k + 1;
    // raw maximum x determined by candies constraint
    var raw := n / denom;
    var mx := raw;
    if mx > M {
      mx := M;
    }

    if mx >= 1 {
      // prove that mx yields a valid distribution (CandiesUsed(mx,d,k) <= n)
      CandiesUsedForChosenX(n, k, M, D, d, raw, mx);
      assert ValidDistribution(mx, d, n, k, M, D);

      var cand := mx * d;
      if cand > best {
        best := cand;
        best_x := mx;
        best_d := d;
        // show updated invariants: bounds and validity
        assert 1 <= best_x <= M;
        assert 1 <= best_d <= D;
        // best == best_x * best_d follows from assignment
        assert best == best_x * best_d;
        // prove best >= 1
        MulLeMonotone(1, best_d, best_x);
        assert 1 <= best;
        // prove best <= M * D
        MulLe2(best_x, best_d, M, D);
        assert best <= M * D;
        assert ValidDistribution(best_x, best_d, n, k, M, D);
      }
    }

    d := d + 1;
  }

  result := best;
  assert result >= 0;
  assert result <= M * D;
  // witness for existence: best_x, best_d
  assert ValidDistribution(best_x, best_d, n, k, M, D);
  assert Person1Candies(best_x, best_d) == result;
  assert exists x: int, dd: int :: x == best_x && dd == best_d && ValidDistribution(x, dd, n, k, M, D) && Person1Candies(x, dd) == result;
}
// </vc-code>

