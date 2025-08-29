// <vc-helpers>
function SumOfDigits(n: nat): nat
{
  if n == 0 then 0 else (n % 10) + SumOfDigits(n / 10)
}

function NatToBinaryString(n: nat): string
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else NatToBinaryString(n / 2) + (if n % 2 == 0 then "0" else "1")
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def solve(n: int) -> str
Given a positive integer N, return the total sum of its digits in binary.
*/
// </vc-description>

// <vc-spec>
method solve(n: int) returns (result: string)
  requires n > 0
  ensures result == NatToBinaryString(SumOfDigits(n))
// </vc-spec>
// <vc-code>
{
  var sum := SumOfDigits(n);
  result := NatToBinaryString(sum);
}
// </vc-code>

function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// pure-end