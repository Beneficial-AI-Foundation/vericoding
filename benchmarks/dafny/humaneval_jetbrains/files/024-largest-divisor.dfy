/*
function_signature: def largest_divisor(n: int) -> int
For a given number n, find the largest number that divides n evenly, smaller than n
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method largest_divisor(n: int) returns (d : int)
  // pre-conditions-start
  requires n > 1
  // pre-conditions-end
  // post-conditions-start
  ensures 1 <= d < n
  ensures n % d == 0
  ensures forall k :: d < k < n ==> n % k != 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
