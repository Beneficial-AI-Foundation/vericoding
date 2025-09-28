// <vc-preamble>
function IsPrime(n: nat) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>
method CheckIsPrime(n: nat) returns (isPrime: bool)
  ensures isPrime == IsPrime(n)
{
  if n <= 1 {
    return false;
  }
  var k := 2;
  while k < n
    invariant 2 <= k <= n
    invariant forall j :: 2 <= j < k ==> n % j != 0
  {
    if n % k == 0 {
      return false;
    }
    k := k + 1;
  }
  return true;
}
// </vc-helpers>

// <vc-spec>
method x_or_y(n: nat, x: int, y: int) returns (result: int)

  ensures IsPrime(n) ==> result == x
  ensures !IsPrime(n) ==> result == y
// </vc-spec>
// <vc-code>
{
  var is_n_prime := CheckIsPrime(n);
  if is_n_prime {
    result := x;
  } else {
    result := y;
  }
}
// </vc-code>
