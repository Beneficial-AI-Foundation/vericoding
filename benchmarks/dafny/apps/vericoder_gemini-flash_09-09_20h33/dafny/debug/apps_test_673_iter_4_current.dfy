predicate ValidInput(n: int, k: int)
{
    n >= 1 && k > 0
}

predicate IsCorrectResult(n: int, k: int, result: int)
    requires k > 0
{
    result > n && result % k == 0 && forall x :: n < x < result ==> x % k != 0
}

// <vc-helpers>
predicate IsDivisible(a: int, b: int) {
  b != 0 && a % b == 0
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures IsCorrectResult(n, k, result)
// </vc-spec>
// <vc-code>
{
  var result_var := (n / k) * k;
  if result_var <= n {
    result_var := result_var + k;
  }
  
  result := result_var;
}
// </vc-code>

