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
lemma ComputeInversionsEquivalence(n: int, k: int, iterations: int)
    requires n >= 1 && k >= 0 && iterations >= 0
    requires iterations <= min(k, n / 2)
    ensures computeInversions(n, k, iterations) == sumInversionsFormula(n, iterations)
    decreases iterations
{
    if iterations == 0 {
        // Base case: both return 0
    } else {
        ComputeInversionsEquivalence(n, k, iterations - 1);
    }
}

lemma SumInversionsNonNegative(n: int, iterations: int)
    requires n >= 1 && iterations >= 0
    requires iterations <= n / 2
    ensures sumInversionsFormula(n, iterations) >= 0
    decreases iterations
{
    if iterations == 0 {
        // Base case: 0 >= 0
    } else {
        SumInversionsNonNegative(n, iterations - 1);
        var term1 := n - 2*(iterations-1) - 1;
        var term2 := n - 2*(iterations-1) - 2;
        // Since iterations <= n/2, we have 2*iterations <= n
        // So 2*(iterations-1) <= n-2, which means term1 >= 1 and term2 >= 0
        assert term1 >= 1;
        assert term2 >= 0;
    }
}

lemma SumInversionsFormulaHelper(n: int, i: int)
    requires n >= 1 && i >= 0 && i <= n / 2
    ensures sumInversionsFormula(n, i) == i * (2 * n - 2 * i - 1)
    decreases i
{
    if i == 0 {
        assert sumInversionsFormula(n, 0) == 0;
        assert 0 * (2 * n - 0 - 1) == 0;
    } else {
        SumInversionsFormulaHelper(n, i - 1);
        assert sumInversionsFormula(n, i - 1) == (i - 1) * (2 * n - 2 * (i - 1) - 1);
        
        var prev := sumInversionsFormula(n, i - 1);
        var term1 := n - 2 * (i - 1) - 1;
        var term2 := n - 2 * (i - 1) - 2;
        
        assert sumInversionsFormula(n, i) == prev + term1 + term2;
        assert prev == (i - 1) * (2 * n - 2 * i + 2 - 1);
        assert prev == (i - 1) * (2 * n - 2 * i + 1);
        
        assert term1 + term2 == (n - 2 * i + 2 - 1) + (n - 2 * i + 2 - 2);
        assert term1 + term2 == (n - 2 * i + 1) + (n - 2 * i);
        assert term1 + term2 == 2 * n - 4 * i + 1;
        
        assert sumInversionsFormula(n, i) == (i - 1) * (2 * n - 2 * i + 1) + (2 * n - 4 * i + 1);
        assert sumInversionsFormula(n, i) == (i - 1) * (2 * n - 2 * i + 1) + (2 * n - 4 * i + 1);
        
        // Expand and simplify
        assert (i - 1) * (2 * n - 2 * i + 1) == 2 * n * i - 2 * n - 2 * i * i + 2 * i + i - 1;
        assert (i - 1) * (2 * n - 2 * i + 1) + (2 * n - 4 * i + 1) == 
               2 * n * i - 2 * n - 2 * i * i + 2 * i + i - 1 + 2 * n - 4 * i + 1;
        assert (i - 1) * (2 * n - 2 * i + 1) + (2 * n - 4 * i + 1) == 
               2 * n * i - 2 * i * i - i;
        assert 2 * n * i - 2 * i * i - i == i * (2 * n - 2 * i - 1);
        
        assert sumInversionsFormula(n, i) == i * (2 * n - 2 * i - 1);
    }
}

lemma MaxInversionsFormula(n: int, iterations: int)
    requires n >= 1 && iterations == n / 2
    ensures sumInversionsFormula(n, iterations) == n * (n - 1) / 2
{
    SumInversionsFormulaHelper(n, iterations);
    assert sumInversionsFormula(n, iterations) == iterations * (2 * n - 2 * iterations - 1);
    
    if n % 2 == 0 {
        assert iterations == n / 2;
        assert sumInversionsFormula(n, iterations) == (n / 2) * (2 * n - n - 1);
        assert sumInversionsFormula(n, iterations) == (n / 2) * (n - 1);
        assert (n / 2) * (n - 1) == n * (n - 1) / 2;
    } else {
        assert n % 2 == 1;
        assert iterations == n / 2;
        assert iterations == (n - 1) / 2;
        assert sumInversionsFormula(n, iterations) == ((n - 1) / 2) * (2 * n - (n - 1) - 1);
        assert sumInversionsFormula(n, iterations) == ((n - 1) / 2) * n;
        assert ((n - 1) / 2) * n == n * (n - 1) / 2;
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
    var sum := 0;
    var i := 0;
    
    while i < iterations
        invariant 0 <= i <= iterations
        invariant sum == computeInversions(n, k, i)
        invariant sum == sumInversionsFormula(n, i)
        invariant sum >= 0
    {
        var term1 := n - 2*i - 1;
        var term2 := n - 2*i - 2;
        sum := sum + term1 + term2;
        i := i + 1;
    }
    
    assert i == iterations;
    assert sum == computeInversions(n, k, iterations);
    assert sum == sumInversionsFormula(n, iterations);
    
    SumInversionsNonNegative(n, iterations);
    assert sum >= 0;
    
    if k >= n / 2 {
        assert iterations == n / 2;
        MaxInversionsFormula(n, iterations);
        assert sum == n * (n - 1) / 2;
    } else {
        assert iterations == k;
        assert k < n / 2;
        assert sum == sumOfConsecutivePairs(n, k);
    }
    
    result := sum;
}
// </vc-code>

