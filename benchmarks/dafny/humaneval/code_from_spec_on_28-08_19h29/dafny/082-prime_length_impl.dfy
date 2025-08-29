function IsPrime(n: int) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>
// No additional helpers needed for this task
// </vc-helpers>

// <vc-description>
/*
function_signature: def prime_length(s: str) -> bool
Write a function that takes a string and returns True if the string length is a prime number or False otherwise
*/
// </vc-description>

// <vc-spec>
method PrimeLength(s: string) returns (result: bool)
  ensures result == IsPrime(|s|)
// </vc-spec>
// <vc-code>
{
  result := IsPrime(|s|);
}
// </vc-code>
