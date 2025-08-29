function IsPrime(n: nat) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def x_or_y(int n, int x, int y) -> int
A simple program which should return the value of x if n is a prime number and should return the value of y otherwise.
*/
// </vc-description>

// <vc-spec>
function x_or_y(n: nat, x: int, y: int): int
  ensures IsPrime(n) ==> x_or_y(n, x, y) == x
  ensures !IsPrime(n) ==> x_or_y(n, x, y) == y
// </vc-spec>
// <vc-code>
{
  if IsPrime(n) then x else y
}
// </vc-code>
