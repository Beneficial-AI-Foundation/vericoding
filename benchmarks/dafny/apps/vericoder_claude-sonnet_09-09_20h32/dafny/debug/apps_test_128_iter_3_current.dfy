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
lemma computeInversionsEquivalence(n: int, k: int, iterations: int)
    requires n >= 1 && k >= 0 && iterations >= 0
    requires iterations <= min(k, n / 2)
    ensures computeInversions(n, k, iterations) == sumInversionsFormula(n, iterations)
    decreases iterations
{
    if iterations == 0 {
        // Base case is trivial
    } else {
        computeInversionsEquivalence(n, k, iterations - 1);
    }
}

lemma sumOfConsecutivePairsEquivalence(n: int, k: int)
    requires n >= 1 && k >= 0 && k < n / 2
    ensures sumOfConsecutivePairs(n, k) == sumInversionsFormula(n, k)
{
    // The definition of sumOfConsecutivePairs directly uses sumInversionsFormula
}

lemma maxInversionsFormula(n: int)
    requires n >= 1
    ensures sumInversionsFormula(n, n / 2) == n * (n - 1) / 2
    decreases n
{
    if n == 1 {
        // Base case: n = 1, n / 2 = 0
        assert sumInversionsFormula(1, 0) == 0;
        assert 1 * (1 - 1) / 2 == 0;
    } else if n == 2 {
        // Base case: n = 2, n / 2 = 1
        assert sumInversionsFormula(2, 1) == (2 - 2*0 - 1) + (2 - 2*0 - 2) == 1 + 0 == 1;
        assert 2 * (2 - 1) / 2 == 1;
    } else {
        // Inductive case
        maxInversionsFormula(n - 2);
        // Prove the inductive step using the recurrence relation
    }
}

lemma sumInversionsFormulaPositive(n: int, iterations: int)
    requires n >= 1 && iterations >= 0 && iterations <= n / 2
    ensures sumInversionsFormula(n, iterations) >= 0
    decreases iterations
{
    if iterations == 0 {
        // Base case
    } else {
        sumInversionsFormulaPositive(n, iterations - 1);
        // The terms being added are non-negative when n >= 1 and iterations <= n / 2
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
    var iterations := min(k, n / 2);
    
    if iterations == 0 {
        result := 0;
    } else {
        result := sumInversionsFormula(n, iterations);
        sumInversionsFormulaPositive(n, iterations);
    }
    
    computeInversionsEquivalence(n, k, iterations);
    
    if k >= n / 2 {
        maxInversionsFormula(n);
    } else {
        sumOfConsecutivePairsEquivalence(n, k);
    }
}
// </vc-code>

