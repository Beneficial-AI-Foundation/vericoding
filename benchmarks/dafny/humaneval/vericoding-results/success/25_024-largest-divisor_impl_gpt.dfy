// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function LPDivFrom(n: int, k: int): int
  requires n > 1
  requires 1 <= k < n
  ensures 1 <= LPDivFrom(n,k) < k + 1
  ensures n % LPDivFrom(n,k) == 0
  ensures forall t :: LPDivFrom(n,k) < t < k + 1 ==> n % t != 0
  decreases k
{
  if n % k == 0 then k else LPDivFrom(n, k - 1)
}

function LPDiv(n: int): int
  requires n > 1
  ensures 1 <= LPDiv(n) < n
  ensures n % LPDiv(n) == 0
  ensures forall k :: LPDiv(n) < k < n ==> n % k != 0
{
  LPDivFrom(n, n - 1)
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
  d := LPDiv(n);
}
// </vc-code>
