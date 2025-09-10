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
lemma computeInversions_eq_sumInversionsFormula(n: int, k: int, iterations: int)
    requires n >= 1 && k >= 0 && iterations >= 0
    requires iterations <= min(k, n / 2)
    ensures computeInversions(n, k, iterations) == sumInversionsFormula(n, iterations)
{
    if iterations == 0 {
    } else {
        calc {
            computeInversions(n, k, iterations);
            computeInversions(n, k, iterations - 1) + (n - 2*(iterations-1) - 1) + (n - 2*(iterations-1) - 2);
            { computeInversions_eq_sumInversionsFormula(n, k, iterations - 1); }
            sumInversionsFormula(n, iterations - 1) + (n - 2*(iterations-1) - 1) + (n - 2*(iterations-1) - 2);
            sumInversionsFormula(n, iterations);
        }
    }
}

lemma sumInversionsFormula_total(n: int)
    requires n >= 1
    ensures sumInversionsFormula(n, n / 2) == n * (n - 1) / 2
{
    if n == 1 {
    } else if n % 2 == 0 {
        calc {
            sumInversionsFormula(n, n / 2);
            sumInversionsFormula(n, n / 2 - 1) + (n - 2*((n/2)-1) - 1) + (n - 2*((n/2)-1) - 2);
            { sumInversionsFormula_total(n); }
            (n - 1) * (n - 2) / 2 + (n - (n - 2) - 1) + (n - (n - 2) - 2);
            (n - 1) * (n - 2) / 2 + 1 + 0;
            (n - 1) * (n - 2) / 2 + 1;
            ((n - 1) * (n - 2) + 2) / 2;
            (n^2 - 3*n + 2 + 2) / 2;
            (n^2 - 3*n + 4) / 2;
            n * (n - 1) / 2;
        }
    } else {
        calc {
            sumInversionsFormula(n, n / 2);
            sumInversionsFormula(n, n / 2 - 1) + (n - 2*((n/2)-1) - 1) + (n - 2*((n/2)-1) - 2);
            { sumInversionsFormula_total(n); }
            (n - 1) * (n - 2) / 2 + (n - (n - 3) - 1) + (n - (n - 3) - 2);
            (n - 1) * (n - 2) / 2 + 2 + 1;
            (n - 1) * (n - 2) / 2 + 3;
            ((n - 1) * (n - 2) + 6) / 2;
            (n^2 - 3*n + 2 + 6) / 2;
            (n^2 - 3*n + 8) / 2;
            n * (n - 1) / 2;
        }
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
    var iterations := min(k, n/2);
    result := computeInversions(n, k, iterations);
    calc {
        result;
        computeInversions(n, k, iterations);
        { computeInversions_eq_sumInversionsFormula(n, k, iterations); }
        sumInversionsFormula(n, iterations);
    }
    if k >= n / 2 {
        calc {
            result;
            sumInversionsFormula(n, n / 2);
            { sumInversionsFormula_total(n); }
            n * (n - 1) / 2;
        }
    } else {
        calc {
            result;
            sumInversionsFormula(n, iterations);
            sumInversionsFormula(n, k);
            sumOfConsecutivePairs(n, k);
        }
    }
}
// </vc-code>

