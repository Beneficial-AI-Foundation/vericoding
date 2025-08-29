// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-description>
/*
function_signature: def largest_divisor(n: int) -> int
For a given number n, find the largest number that divides n evenly, smaller than n
*/
// </vc-description>

// <vc-spec>
method largest_divisor(n: int) returns (d: int)
  requires n > 0
  ensures 1 <= d < n
  ensures n % d == 0
  ensures forall k :: d < k < n ==> n % k != 0
// </vc-spec>
// <vc-code>
{
  d := 1;
  var k := n - 1;
  while k > 1
    invariant 1 <= d < n
    invariant 1 <= k < n
    invariant n % d == 0
    invariant forall m :: d < m <= k ==> n % m != 0
  {
    if n % k == 0 {
      d := k;
      break;
    }
    k := k - 1;
  }
}
// </vc-code>
