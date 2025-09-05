
/*
function_signature: def count_up_to(n : int) -> list[int]
Implement a function that takes an non-negative integer and returns an array of the first n integers that are prime numbers and less than n.
*/

function IsPrime(n: int) : bool
{
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}

method CountUpTo(n: int) returns (primes: seq<int>)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |primes| ==> IsPrime(primes[i])
  ensures forall i :: 0 <= i < |primes| ==> primes[i] < n
  ensures forall p :: 2 <= p < n && IsPrime(p) <==> p in primes
  // post-conditions-end
{
  assume false;
}
