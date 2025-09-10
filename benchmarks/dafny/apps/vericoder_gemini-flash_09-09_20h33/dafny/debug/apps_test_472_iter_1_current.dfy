function digitSum(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else (n % 10) + digitSum(n / 10)
}

// <vc-helpers>
function f(x: int): int {
  x * x + digitSum(x) * x
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires n >= 1
  ensures n == 1 ==> result == -1
  ensures n > 1 && result > 0 ==> result * result + digitSum(result) * result == n
  ensures n > 1 && result > 0 ==> forall y :: y > 0 && y < result ==> y * y + digitSum(y) * y != n
  ensures n > 1 && result == -1 ==> forall x :: x > 0 ==> x * x + digitSum(x) * x != n
  ensures result == -1 || result > 0
// </vc-spec>
// <vc-code>
{
  var x := 1;
  while f(x) < n
    invariant x >= 1
    // The invariant f(x) < n ensures that the loop continues as long as f(x) is less than n.
    // This allows us to search for a potential solution.
  {
    x := x + 1;
  }
  if f(x) == n then
    result := x
  else
    result := -1;
}
// </vc-code>

