function min(a: int, b: int): int
    ensures min(a, b) == a || min(a, b) == b
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a ==> a <= b
    ensures min(a, b) == b ==> b <= a
{
    if a <= b then a else b
}

function computeInversions(n: int, k: int, iterations: int): int
    requires n >= 1 && k >= 0 && iterations >= 0
    requires iterations <= min(k, n / 2)
    decreases iterations
{
    if iterations == 0 then 0
    else computeInversions(n, k, iterations - 1) + (n - 2*(iterations-1) - 1) + (n - 2*(iterations-1) - 2)
}

function sumInversionsFormula(n: int, iterations: int): int
    requires n >= 1 && iterations >= 0
    requires iterations <= n / 2
    decreases iterations
{
    if iterations == 0 then 0
    else sumInversionsFormula(n, iterations - 1) + (n - 2*(iterations-1) - 1) + (n - 2*(iterations-1) - 2)
}

function sumOfConsecutivePairs(n: int, k: int): int
    requires n >= 1 && k >= 0 && k < n / 2
{
    var iterations := k;
    if iterations == 0 then 0
    else sumInversionsFormula(n, iterations)
}

// <vc-helpers>
lemma MinLeRight(a: int, b: int)
    ensures min(a, b) <= b
{
    if a <= b {
        assert min(a, b) == a;
        assert a <= b;
    } else {
        assert min(a, b) == b;
        assert b <= b;
    }
    assert min(a, b) <= b;
}

lemma TwiceFloorLeq(n: int)
    requires n >= 0
    ensures 2 * (n / 2) <= n
{
    var r := n % 2;
    assert 0 <= r && r < 2;
    assert n == 2 * (n / 2) + r;
    assert 2 * (n / 2) <= n;
}

lemma SumFormula(n: int, t: int)
    requires n >= 1 && t >= 0 && t <= n / 2
    ensures sumInversionsFormula(n, t) == t * (2 * n - 2 * t - 1)
    decreases t
{
    if t == 0 {
        assert sumInversionsFormula(n, 0) == 0;
        assert 0 == 0 * (2 * n - 2 * 0 - 1);
    } else {
        // Inductive hypothesis
        SumFormula(n, t - 1);
        assert sumInversionsFormula(n, t - 1) == (t - 1) * (2 * n - 2 * (t - 1) - 1);

        // Unfold definition for t
        assert sumInversionsFormula(n, t) ==
               sumInversionsFormula(n, t - 1) + (n - 2 * (t - 1) - 1) + (n - 2 * (t - 1) - 2);

        // Substitute the inductive hypothesis
        var a := (t - 1) * (2 * n - 2 * (t - 1) - 1);
        var b := (n - 2 * (t - 1) - 1) + (n - 2 * (t - 1) - 2);
        assert sumInversionsFormula(n, t) == a + b;

        // Simplify algebraically to t * (2*n - 2*t - 1)
        // Compute a = (t-1)*(2*n - 2*t + 1)
        assert a == (t - 1) * (2 * n - 2 * t + 1);

        // Compute b = 2*n - 4*t + 1
        assert b == 2 * n - 4 * t + 1;

        // Now expand and simplify a + b to get t*(2*n - 2*t - 1)
        // a + b = 2*n*t - 2*t*t - t
        assert a + b == t * (2 * n - 2 * t - 1);

        assert sumInversionsFormula(n, t) == t * (2 * n - 2 * t - 1);
    }
}

lemma ComputeEqualsSum(n: int, k: int, iterations: int)
    requires n >= 1 && k >= 0 && iterations >= 0
    requires iterations <= min(k, n / 2)
    ensures computeInversions(n, k, iterations) == sumInversionsFormula(n, iterations)
    decreases iterations
{
    if iterations == 0 {
        assert computeInversions(n, k, 0) == 0;
        assert sumInversionsFormula(n, 0) == 0;
    } else {
        // iterations > 0
        assert iterations - 1 >= 0;
        // iterations - 1 <= min(k, n/2)
        assert iterations - 1 <= min(k, n / 2);
        ComputeEqualsSum(n, k, iterations - 1);
        // Unfold both definitions and use the induction hypothesis
        assert computeInversions(n, k, iterations) ==
               computeInversions(n, k, iterations - 1) + (n - 2 * (iterations - 1) - 1) + (n - 2 * (iterations - 1) - 2);
        assert sumInversionsFormula(n, iterations) ==
               sumInversionsFormula(n, iterations - 1) + (n - 2 * (iterations - 1) - 1) + (n - 2 * (iterations - 1) - 2);

        assert computeInversions(n, k, iterations - 1) == sumInversionsFormula(n, iterations - 1);
        assert computeInversions(n, k, iterations) == sumInversionsFormula(n, iterations);
    }
}

lemma MinWhenKGeN2(k: int, n: int)
    requires n >= 1 && k >= 0
    requires k >= n / 2
    ensures min(k, n / 2) == n / 2
{
    if k <= n / 2 {
        // then k == n/2
        assert k == n / 2;
        assert min(k, n / 2) == k;
        assert min(k, n / 2) == n / 2;
    } else {
        // k > n/2
        assert !(k <= n / 2);
        assert min(k, n / 2) == n / 2;
    }
}

lemma MinWhenKLtN2(k: int, n: int)
    requires n >= 1 && k >= 0
    requires k < n / 2
    ensures min(k, n / 2) == k
{
    // k < n/2 implies k <= n/2, hence min is k
    assert k <= n / 2;
    assert min(k, n / 2) == k;
}

lemma SumOfConsecutivePairsEquals(n: int, k: int)
    requires n >= 1 && k >= 0 && k < n / 2
    ensures sumOfConsecutivePairs(n, k) == sumInversionsFormula(n, k)
{
    var iterations := k;
    if iterations == 0 {
        assert sumOfConsecutivePairs(n, k) == 0;
        assert sumInversionsFormula(n, k) == 0;
    } else {
        assert sumOfConsecutivePairs(n, k) == sumInversionsFormula(n, iterations);
        assert sumInversionsFormula(n, iterations) == sumInversionsFormula(n, k);
    }
}

lemma SumInversionsNonNeg(n: int, t: int)
    requires n >= 1 && t >= 0 && t <= n / 2
    ensures sumInversionsFormula(n, t) >= 0
{
    SumFormula(n, t);
    assert sumInversionsFormula(n, t) == t * (2 * n - 2 * t - 1);

    // From t <= n/2 we get 2*t <= 2*(n/2)
    assert 2 * t <= 2 * (n / 2);
    // And 2*(n/2) <= n
    TwiceFloorLeq(n);
    assert 2 * (n / 2) <= n;
    // Hence 2*t <= n
    assert 2 * t <= n;

    // Therefore 2*n - 2*t - 1 >= 2*n - n - 1 = n - 1 >= 0 (since n >= 1)
    assert 2 * n - 2 * t - 1 >= 2 * n - n - 1;
    assert 2 * n - n - 1 == n - 1;
    assert n - 1 >= 0;
    assert 2 * n - 2 * t - 1 >= 0;

    // t >= 0 and the other factor >= 0 imply product >= 0
    assert t * (2 * n - 2 * t - 1) >= 0;
    assert sumInversionsFormula(n, t) >= 0;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires n >= 1 && k >= 0
    ensures result >= 0
    ensures result == computeInversions(n, k, min(k, n / 2))
    ensures result == sumInversionsFormula(n, min(k, n / 2))
    ensures k >= n / 2 ==> result == n * (n - 1) / 2
    ensures k < n / 2 ==> result == sumOfConsecutivePairs(n, k)
// </vc-spec>
// <vc-code>
{
  var iterations := min(k, n / 2);
  // Directly set result to the defined function value
  result := computeInversions(n, k, iterations);

  // Establish equality with sumInversionsFormula
  ComputeEqualsSum(n, k, iterations);

  // iterations <= n/2 so we can prove non-negativity of the formula
  assert iterations <= n / 2;
  SumInversionsNonNeg(n, iterations);

  // Non-negativity follows because the formula yields a non-negative count
  assert result == sumInversionsFormula(n, iterations);
  assert result >= 0;

  if k >= n / 2 {
    // iterations == n/2 in this case
    MinWhenKGeN2(k, n);
    assert iterations == n / 2;

    // Use closed form to show full inversion count
    SumFormula(n, iterations);
    assert sumInversionsFormula(n, iterations) == iterations * (2 * n - 2 * iterations - 1);

    // Show this equals n*(n-1)/2 when iterations == n/2
    var r := n % 2;
    assert 0 <= r && r < 2;
    assert n == 2 * (n / 2) + r;

    if r == 0 {
      // n = 2*iterations
      assert iterations * (2 * n - 2 * iterations - 1) == n * (n - 1) / 2;
    } else {
      // r == 1, n = 2*iterations + 1
      assert iterations * (2 * n - 2 * iterations - 1) == n * (n - 1) / 2;
    }
    assert result == n * (n - 1) / 2;
  } else {
    // k < n/2: iterations == k and sumOfConsecutivePairs returns sumInversionsFormula(n,k)
    MinWhenKLtN2(k, n);
    assert iterations == k;
    SumOfConsecutivePairsEquals(n, k);
    assert sumOfConsecutivePairs(n, k) == sumInversionsFormula(n, k);
    assert result == sumOfConsecutivePairs(n, k);
  }
}
// </vc-code>

