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
lemma computeInversions_equals_sumInversionsFormula(n: int, k: int, iterations: int)
  requires n >= 1 && k >= 0 && iterations >= 0
  requires iterations <= min(k, n / 2)
  ensures computeInversions(n, k, iterations) == sumInversionsFormula(n, iterations)
  decreases iterations
{
  if iterations > 0 {
    computeInversions_equals_sumInversionsFormula(n, k, iterations - 1);
  }
}

lemma sumInversionsFormula_closed_form(n: int, iterations: int)
  requires n >= 1 && iterations >= 0
  requires iterations <= n / 2
  ensures sumInversionsFormula(n, iterations) == iterations * (2*n - 2*iterations - 1)
{
  if iterations == 0 {
    assert sumInversionsFormula(n, 0) == 0;
    assert 0 * (2*n - 2*0 - 1) == 0;
  } else {
    sumInversionsFormula_closed_form(n, iterations - 1);
    calc {
      sumInversionsFormula(n, iterations);
      sumInversionsFormula(n, iterations - 1) + (n - 2*(iterations-1) - 1) + (n - 2*(iterations-1) - 2);
      (iterations - 1) * (2*n - 2*(iterations - 1) - 1) + (n - 2*iterations + 2 - 1) + (n - 2*iterations + 2 - 2);
      (iterations - 1) * (2*n - 2*iterations + 2 - 1) + (n - 2*iterations + 1) + (n - 2*iterations);
      (iterations - 1) * (2*n - 2*iterations + 1) + 2*n - 4*iterations + 1;
      (iterations - 1) * (2*n - 2*iterations + 1) + 2*n - 4*iterations + 1;
      iterations * (2*n - 2*iterations + 1) - (2*n - 2*iterations + 1) + 2*n - 4*iterations + 1;
      iterations * (2*n - 2*iterations + 1) - 2*n + 2*iterations - 1 + 2*n - 4*iterations + 1;
      iterations * (2*n - 2*iterations + 1) - 2*iterations;
      iterations * (2*n - 2*iterations + 1 - 2);
      iterations * (2*n - 2*iterations - 1);
    }
  }
}

lemma sumOfConsecutivePairs_closed_form(n: int, k: int)
  requires n >= 1 && k >= 0 && k < n / 2
  ensures sumOfConsecutivePairs(n, k) == k * (2*n - 2*k - 1)
{
  sumInversionsFormula_closed_form(n, k);
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
    var num_iterations := min(k, n / 2);
    computeInversions_equals_sumInversionsFormula(n, k, num_iterations);
    sumInversionsFormula_closed_form(n, num_iterations);

    result := num_iterations * (2*n - 2*num_iterations - 1);

    if k >= n / 2 {
        calc {
            num_iterations;
            min(k, n / 2);
            n / 2;
        }
        assert num_iterations == n / 2;
        calc {
            result;
            (n / 2) * (2*n - 2*(n / 2) - 1);
            (n / 2) * (2*n - n - 1);
            (n / 2) * (n - 1);
            n * (n - 1) / 2;
        }
    } else { // k < n / 2
        calc {
            num_iterations;
            min(k, n / 2);
            k;
        }
        assert num_iterations == k;
        sumOfConsecutivePairs_closed_form(n, k);
        calc {
            result;
            k * (2*n - 2*k - 1);
            sumOfConsecutivePairs(n, k);
        }
    }
}
// </vc-code>

