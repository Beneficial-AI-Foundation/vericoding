// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate isDivisor(n: int, d: int)
  requires n > 0 && d > 0
{
  n % d == 0
}

function largestDivisorBelow(n: int, k: int): int
  requires n > 1 && 1 <= k < n
  decreases k
{
  if k == 1 then 1
  else if n % k == 0 then k
  else largestDivisorBelow(n, k - 1)
}

lemma largestDivisorBelowProperties(n: int, k: int)
  requires n > 1 && 1 <= k < n
  ensures 1 <= largestDivisorBelow(n, k) <= k
  ensures n % largestDivisorBelow(n, k) == 0
  ensures forall j :: largestDivisorBelow(n, k) < j <= k ==> n % j != 0
  decreases k
{
  if k == 1 {
  } else if n % k == 0 {
  } else {
    largestDivisorBelowProperties(n, k - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method largest_divisor(n: int) returns (d : int)

  requires n > 1

  ensures 1 <= d < n
  ensures n % d == 0
  ensures forall k :: d < k < n ==> n % k != 0
// </vc-spec>
// <vc-code>
{
  d := largestDivisorBelow(n, n - 1);
  largestDivisorBelowProperties(n, n - 1);
}
// </vc-code>
