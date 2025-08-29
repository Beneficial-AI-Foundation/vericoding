// <vc-helpers>
predicate IsPrime(n: int)
{
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def is_prime(n)
Return true if a given number is prime, and false otherwise.
*/
// </vc-description>

// <vc-spec>
method is_prime(n: int) returns (result: bool)
  ensures result == IsPrime(n)
// </vc-spec>
// <vc-code>
{
  if n <= 1 {
    return false;
  }
  if n == 2 {
    return true;
  }
  if n % 2 == 0 {
    return false;
  }
  
  var i := 3;
  while i * i <= n
    invariant i % 2 == 1
    invariant forall k :: 2 <= k < i ==> n % k != 0
  {
    if n % i == 0 {
      return false;
    }
    i := i + 2;
  }
  assert forall k :: 2 <= k < n ==> (k % 2 == 0 || k >= i || n % k != 0);
  return true;
}
// </vc-code>
