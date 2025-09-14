// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No changes to helper, it was not the cause of the verification error.*/
function abs(x: int): int { if x < 0 then -x else x }
// </vc-helpers>

// <vc-spec>
method multiply(a: int, b: int) returns (result: int)
    ensures result == a * b
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): The previous implementation had an issue with handling negative numbers and ensuring the invariant held. This version simplifies the approach by always iterating on the absolute value of B and adjusting the final sign. */
{
  var res := 0;
  var i := 0;

  // Handle cases where a or b is zero directly.
  if a == 0 || b == 0 {
    result := 0;
    return;
  }

  // Determine the sign of the result
  var finalSign := 1;
  if (a < 0 && b > 0) || (a > 0 && b < 0) {
    finalSign := -1;
  }

  // Perform multiplication using absolute values
  var abs_a := abs(a);
  var abs_b := abs(b);

  while i < abs_b
    invariant i >= 0
    invariant i <= abs_b
    invariant res == i * abs_a
    decreases abs_b - i
  {
    res := res + abs_a;
    i := i + 1;
  }

  result := finalSign * res;
}
// </vc-code>
