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
lemma ComputeEqualsSum(n: int, k: int, it: int)
    requires n >= 1 && k >= 0 && it >= 0 && it <= min(k, n / 2)
    ensures computeInversions(n, k, it) == sumInversionsFormula(n, it)
    decreases it
{
    if it == 0 {
        // both sides are 0 by definition
    } else {
        // Unfold definitions
        assert computeInversions(n, k, it) ==
            computeInversions(n, k, it - 1) + (n - 2*(it - 1) - 1) + (n - 2*(it - 1) - 2);
        assert sumInversionsFormula(n, it) ==
            sumInversionsFormula(n, it - 1) + (n - 2*(it - 1) - 1) + (n - 2*(it - 1) - 2);

        ComputeEqualsSum(n, k, it - 1);
        assert computeInversions(n, k, it - 1) == sumInversionsFormula(n, it - 1);

        // therefore the two unfolded expressions are equal
        assert computeInversions(n, k, it) == sumInversionsFormula(n, it);
    }
}

lemma SumFormula(n: int, t: int)
    requires n >= 1 && t >= 0 && t <= n / 2
    ensures sumInversionsFormula(n, t) == t * (2 * n - 2 * t - 1)
    decreases t
{
    if t == 0 {
        // sumInversionsFormula(n,0) == 0 and RHS == 0
    } else {
        assert sumInversionsFormula(n, t) ==
            sumInversionsFormula(n, t - 1) + (n - 2*(t - 1) - 1) + (n - 2*(t - 1) - 2);
        SumFormula(n, t - 1);
        // Now perform the algebraic simplification:
        // (t-1)*(2*n - 2*(t-1) -1) + (n - 2*(t-1) -1) + (n - 2*(t-1) -2)
        // = t*(2*n - 2*t -1)
        assert (t - 1) * (2 * n - 2 * (t - 1) - 1)
               + (n - 2 * (t - 1) - 1)
               + (n - 2 * (t - 1) - 2)
               == t * (2 * n - 2 * t - 1);
        // Combine with previous equalities
        assert sumInversionsFormula(n, t) == t * (2 * n - 2 * t - 1);
    }
}

lemma SumOfConsecutivePairsEquals(n: int, k: int)
    requires n >= 1 && k >= 0 && k < n / 2
    ensures sumOfConsecutivePairs(n, k) == sumInversionsFormula(n, k)
{
    if k == 0 {
        // sumOfConsecutivePairs returns 0 and sumInversionsFormula(n,0)==0
    } else {
        // sumOfConsecutivePairs returns sumInversionsFormula(n,k)
    }
}

lemma MinWhenKGeN2(k: int, n: int)
    requires n >= 0 && k >= n / 2
    ensures min(k, n / 2) == n / 2
{
    if k <= n / 2 {
        // then k == n/2 and min returns k which equals n/2
    } else {
        // k > n/2, min returns n/2
    }
}

lemma MinWhenKLtN2(k: int, n: int)
    requires n >= 0 && k < n / 2
    ensures min(k, n / 2) == k
{
    // If k < n/2 then k <= n/2 is true, so min returns k
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

