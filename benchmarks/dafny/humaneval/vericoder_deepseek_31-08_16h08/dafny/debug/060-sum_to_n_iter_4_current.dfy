

// <vc-helpers>
lemma SumFormula(n: int)
  requires n >= 0
  ensures n * (n + 1) / 2 == if n == 0 then 0 else n + ((n - 1) * n) / 2
{
  if n > 0 {
    calc {
      n * (n + 1) / 2;
      ==
      n + (n * (n - 1)) / 2;
    }
  }
}

lemma SumFormulaZero()
  ensures 0 * (0 + 1) / 2 == 0
{
}
// </vc-helpers>
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
    SumFormulaZero();
    return 0;
  }
  
  var i := 0;
  r := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant r == i * (i + 1) / 2
  {
    i := i + 1;
    r := r + i;
  }
  SumFormula(n);
}
// </vc-code>

