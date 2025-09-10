predicate ValidInput(n: int, k: int) {
    n >= 1 && k >= 2
}

function ImpossibilityCondition(n: int, k: int): bool
    requires ValidInput(n, k)
{
    2 * (n - 1) - k * (k - 1) > 0
}

predicate ValidSolution(n: int, k: int, result: int)
    requires ValidInput(n, k)
{
    if ImpossibilityCondition(n, k) then
        result == -1
    else
        result >= 0 && result <= k &&
        exists x: int :: 
            x >= 0 && 
            x * x - x + (2 * (n - 1) - k * (k - 1)) <= 0 && 
            (x == 0 || (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1)) > 0) &&
            result == k - x
}

// <vc-helpers>
lemma f_kplus1_positive(n: int, k: int)
    requires ValidInput(n, k)
    ensures (k+1)*(k+1) - (k+1) + (2*(n-1) - k*(k-1)) > 0
{
    calc {
        (k+1)*(k+1) - (k+1) + (2*(n-1) - k*(k-1));
        == k*k + 2*k + 1 - k - 1 + 2*n - 2 - k*k + k;
        == 2*k + 2*n - 2;
        == 2*(k + n - 1);
    }
    assert k >= 2 && n >= 1;
    assert k + n - 1 >= 2;
    assert 2*(k + n - 1) > 0;
}

lemma f_k_nonneg_at_k(n: int, k: int)
    requires ValidInput(n, k)
    ensures k*k - k + (2*(n-1) - k*(k-1)) >= 0
{
    calc {
        k*k - k + (2*(n-1) - k*(k-1));
        == k*k - k + 2*n - 2 - k*k + k;
        == 2*n - 2;
        == 2*(n-1);
    }
    assert n >= 1;
    assert 2*(n-1) >= 0;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures result >= -1
    ensures (result == -1) <==> ImpossibilityCondition(n, k)
    ensures ValidSolution(n, k, result)
// </vc-spec>
// <vc-code>
{
  var D := 2 * (n - 1) - k * (k - 1);
  if D > 0 {
    result := -1;
    return;
  }
  var x := 0;
  // Invariant: 0 <= x <= k and f(x) <= 0
  while x < k && (x + 1) * (x + 1) - (x + 1) + D <= 0
    invariant 0 <= x <= k
    invariant x * x - x + D <= 0
    decreases k - x
  {
    x := x + 1;
  }
  // After loop, either x == 0 or f(x+1) > 0
  if x != 0 {
    if x < k {
      // loop termination gives f(x+1) > 0
      assert (x + 1) * (x + 1) - (x + 1) + D > 0;
    } else {
      // x == k; use lemma to show f(k+1) > 0
      f_kplus1_positive(n, k);
      assert (x + 1) * (x + 1) - (x + 1) + D > 0;
    }
  }
  result := k - x;
}
// </vc-code>

