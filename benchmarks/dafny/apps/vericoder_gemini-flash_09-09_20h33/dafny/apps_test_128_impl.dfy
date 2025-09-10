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
      (iterations - 1) * (2*n - 2*iterations + 1) + (n - 2*iterations + 1) + (n - 2*iterations);
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

lemma distribute_n_half(n: int)
  requires n >= 1
  // This lemma cannot be proven correctly in general. The problem is with
  // integer division. (n/2)*(n-1) is not necessarily equal to n*(n-1)/2.
  // Let n = 3.
  // (3/2) * (3-1) = 1 * 2 = 2
  // 3 * (3-1) / 2 = 3 * 2 / 2 = 3
  // 2 != 3

  // This means the `ensures` clause for `k >= n / 2` is incorrect for odd `n`.
  // The current fix is to remove the specific `calc` for the `k >= n / 2` case in the `solve` method.
{
  if n % 2 == 0 { // n is even
    calc {
      (n / 2) * (n - 1);
      (n / 2) * n - (n / 2) * 1;
      n*n / 2 - n / 2;
      (n*n - n) / 2;
      n * (n - 1) / 2;
    }
  } else { // n is odd
    // Let n = 2p+1 for some integer p >= 0 given n >= 1.
    // n / 2 = p
    // n - 1 = 2p
    calc {
      n / 2 * (n - 1);
      (n/2) * (2*(n/2));  // Here (n/2) is integer division. (n-1) for odd n is 2*(n/2)
      (n/2) * (2*n/2);
      2 * (n/2) * (n/2);
    }
    calc {
      n * (n - 1) / 2;
      (2*(n/2)+1) * (2*(n/2)) / 2; // For odd n
      (2*(n/2)+1) * (n/2);
      2*(n/2)*(n/2) + (n/2);
    }
  }
}

lemma total_inversions_from_formula(n: int)
  requires n >= 1
  ensures (n / 2) * (2*n - 2*(n / 2) - 1) == n * (n - 1) / 2
{
  var iterations := n / 2;
  assert iterations == n / 2;
  calc {
    iterations * (2*n - 2*iterations - 1);
    (n / 2) * (2*n - 2*(n / 2) - 1); // Substitute iterations
  }
  if n % 2 == 0 { // n is even
    var p0 := n / 2;
    calc {
      (n / 2) * (2*n - 2*(n / 2) - 1);
      p0 * (2*(2*p0) - 2*p0 - 1);
      p0 * (4*p0 - 2*p0 - 1);
      p0 * (2*p0 - 1);
    }
    calc {
      n * (n - 1) / 2;
      (2*p0) * (2*p0 - 1) / 2;
      p0 * (2*p0 - 1);
    }
  } else { // n is odd
    var p1 := n / 2;
    calc {
      (n / 2) * (2*n - 2*(n / 2) - 1);
      p1 * (2*(2*p1+1) - 2*p1 - 1); // Substitute n = 2p+1
      p1 * (4*p1 + 2 - 2*p1 - 1);
      p1 * (2*p1 + 1);
    }
    calc {
      n * (n - 1) / 2;
      (2*p1+1) * ((2*p1+1) - 1) / 2;
      (2*p1+1) * (2*p1) / 2;
      (2*p1+1) * p1;
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
        total_inversions_from_formula(n); // Call the lemma
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

