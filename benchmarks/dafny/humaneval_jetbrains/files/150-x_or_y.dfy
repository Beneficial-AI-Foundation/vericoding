/*
function_signature: def x_or_y(int n, int x, int y) -> int
A simple program which should return the value of x if n is a prime number and should return the value of y otherwise.
*/

function IsPrime(n: nat) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method x_or_y(n: nat, x: int, y: int) returns (result: int)
  // post-conditions-start
  ensures IsPrime(n) ==> result == x
  ensures !IsPrime(n) ==> result == y
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
