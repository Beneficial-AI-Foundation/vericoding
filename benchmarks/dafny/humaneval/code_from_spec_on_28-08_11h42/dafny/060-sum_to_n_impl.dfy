// <vc-helpers>
lemma SumFormula(k: int)
  requires k >= 0
  ensures k * (k + 1) / 2 == if k == 0 then 0 else (k - 1) * k / 2 + k
{
  if k == 0 {
    assert k * (k + 1) / 2 == 0;
  } else {
    calc {
      k * (k + 1) / 2;
    ==
      (k * (k + 1)) / 2;
    ==
      (k * k + k) / 2;
    ==
      ((k - 1) * k + k + k) / 2;
    ==
      ((k - 1) * k + 2 * k) / 2;
    ==
      ((k - 1) * k) / 2 + (2 * k) / 2;
    ==
      (k - 1) * k / 2 + k;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method sum_to_n(n: int) returns (r : int)
  // post-conditions-start
  ensures r == n * (n + 1) / 2
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n <= 0 {
    r := n * (n + 1) / 2;
  } else {
    r := 0;
    var i := 1;
    while i <= n
      invariant 1 <= i <= n + 1
      invariant r == (i - 1) * i / 2
      decreases n - i + 1
    {
      SumFormula(i);
      r := r + i;
      i := i + 1;
    }
    assert i == n + 1;
    assert r == n * (n + 1) / 2;
  }
}
// </vc-code>
