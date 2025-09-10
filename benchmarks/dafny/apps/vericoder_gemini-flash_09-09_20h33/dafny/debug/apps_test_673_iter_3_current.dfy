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
  var current_n := n;
  var res := 0;

  while res == 0
    decreases
      if current_n % k != 0 then k - (current_n % k) else 0,
      k - (current_n % k)
    invariant current_n >= n
    invariant res == 0 ==> current_n < n + k
  {
    current_n := current_n + 1;
    if current_n % k == 0 {
      res := current_n;
    }
  }
  result := res;
}
// </vc-code>

