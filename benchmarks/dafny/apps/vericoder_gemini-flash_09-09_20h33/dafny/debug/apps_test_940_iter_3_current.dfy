predicate ValidInput(a: int, b: int, c: int)
{
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
}

predicate IsTriangle(a: int, b: int, c: int)
{
    a + b > c && a + c > b && b + c > a
}

function MinOperationsNeeded(a: int, b: int, c: int): int
    requires ValidInput(a, b, c)
{
    var max_val := max(max(a, b), c);
    var sum_of_other_two := a + b + c - max_val;
    max(0, max_val - sum_of_other_two + 1)
}

// <vc-helpers>
function max(x: int, y: int): int
{
  if x < y then y else x
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int) returns (result: int)
    requires ValidInput(a, b, c)
    ensures result >= 0
    ensures result == MinOperationsNeeded(a, b, c)
    ensures result == 0 <==> IsTriangle(a, b, c)
// </vc-spec>
// <vc-code>
{
  var max_val := max(max(a, b), c);
  var sum_of_other_two := a + b + c - max_val;
  if IsTriangle(a, b, c) then
    result := 0;
  else
    result := max(0, max_val - sum_of_other_two + 1);
  // The while loop in the original code seems to be related to handling negative results.
  // However, given the definition of MinOperationsNeeded, the result should never be negative.
  // The definition of MinOperationsNeeded already ensures the result is at least 0.
  // Therefore, this loop is not necessary and might have been an attempt to fix a perceived issue
  // that is already handled by the mathematical definition.
  // Removing the unnecessary loop as the `max(0, ...)` correctly handles the lower bound.
  // while result < 0
  //   invariant result == max_val - sum_of_other_two + 1 || result == 0
  //   invariant max_val == max(max(a,b),c)
  //   invariant sum_of_other_two == a + b + c - max_val
  // {
  //     result := 0;
  // }
}
// </vc-code>

