// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsEven(n: int) { n % 2 == 0 }
predicate Ge8(n: int) { n >= 8 }
// </vc-helpers>

// <vc-spec>
method is_equal_to_sum_even(n: int) returns (b : bool)

  ensures b <==> n % 2 == 0 && n >= 8
// </vc-spec>
// <vc-code>
{
  b := IsEven(n) && Ge8(n);
}
// </vc-code>
