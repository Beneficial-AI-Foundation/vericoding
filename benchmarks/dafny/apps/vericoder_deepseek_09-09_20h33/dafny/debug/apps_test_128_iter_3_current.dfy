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
lemma sumInversionsFormulaClosedForm(n: int, iterations: int) returns (s: int)
    requires n >= 1 && iterations >= 0
    requires iterations <= n / 2
    ensures s == sumInversionsFormula(n, iterations)
    ensures s == iterations * (2*n - 2*iterations - 1)
    decreases iterations
{
    if iterations == 0 {
        s := 0;
    } else {
        var prev := sumInversionsFormulaClosedForm(n, iterations - 1);
        s := prev + (n - 2*(iterations-1) - 1) + (n - 2*(iterations-1) - 2);
        assert s == prev + 2*n - 4*(iterations-1) - 3;
        assert s == (iterations-1)*(2*n - 2*(iterations-1) - 1) + 2*n - 4*(iterations-1) - 3;
        assert s == (iterations-1)*(2*n - 2*iterations + 2 - 1) + 2*n - 4*iterations + 4 - 3;
        assert s := (iterations-1)*(2*n - 2*iterations + 1) + 2*n - 4*iterations + 1;
        assert s == (2*n*iterations - 2*n - 2*(iterations*iterations) + 2*iterations + iterations - 1) + 2*n - 4*iterations + 1;  // Fixed: Replace ^ with explicit multiplication
        assert s == 2*n*iterations - 2*n - 2*(iterations*iterations) + 2*iterations + iterations - 1 + 2*n - 4*iterations + 1;
        assert s == 2*n*iterations - 2*(iterations*iterations) - iterations;
        assert s == iterations * (2*n - 2*iterations - 1);
    }
}

lemma computeInversionsEqualsSumInversions(n: int, k: int, iterations: int)
    requires n >= 1 && k >= 0 && iterations >= 0
    requires iterations <= min(k, n / 2)
    ensures computeInversions(n, k, iterations) == sumInversionsFormula(n, iterations)
    decreases iterations
{
    if iterations > 0 {
        computeInversionsEqualsSumInversions(n, k, iterations - 1);
    }
}

lemma sumOfConsecutivePairsFormula(n: int, k: int)
    requires n >= 1 && k >= 0 && k < n / 2
    ensures sumOfConsecutivePairs(n, k) == sumInversionsFormula(n, k)
{
}

lemma fullInversionsCase(n: int)
    requires n >= 1
    ensures sumInversionsFormula(n, n / 2) == n * (n - 1) / 2
{
    var s := sumInversionsFormulaClosedForm(n, n / 2);
    if n % 2 == 0 {
        assert s == (n/2) * (2*n - 2*(n/2) - 1);
        assert s == (n/2) * (2*n - n - 1);
        assert s == (n/2) * (n - 1);
        assert s == n * (n - 1) / 2;
    } else {
        var half := (n-1)/2;
        assert s == half * (2*n - 2*half - 1);
        assert s == half * (2*n - (n-1) - 1);
        assert s == half * (n);
        assert s == (n-1)/2 * n;
        assert s == n * (n - 1) / 2;
    }
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
    var iters := min(k, n / 2);
    if k >= n / 2 {
        result := n * (n - 1) / 2;
        fullInversionsCase(n);
        computeInversionsEqualsSumInversions(n, k, iters);
    } else {
        sumOfConsecutivePairsFormula(n, k);
        var s_real := iterations * (2*n - 2*iters - 1);
        result := s_real;
        computeInversionsEqualsSumInversions(n, k, iters);
    }
}
// </vc-code>

