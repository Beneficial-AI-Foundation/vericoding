

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*
function_signature: def starts_one_ends(n: int) -> int
Given a positive integer n, return the count of the numbers of n-digit positive integers that start or end with 1. Note: For reviewer, I believe this is the most straightforward spec, and I am relying on Set cardianlity not being computable in general. The point of this problem is really to privide a formula. Note: But I guess a program that goes through each number and adds 1 will be the same as a program that computes in O(1) under this view.
*/
// </vc-description>

// <vc-spec>
method CountNumbersStartingOrEndingWithOne(n: nat) returns (count: nat)
    // pre-conditions-start
    requires n > 0
    // pre-conditions-end
    // post-conditions-start
    ensures n == 1 ==> count == 1
    ensures n > 1 ==> count == 18 * Pow(10, n - 2)
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
  if n == 1 {
    count := 1;
  } else {
    count := 18 * Pow(10, n - 2);
  }
}
// </vc-code>

function Pow(base: nat, exponent: nat): nat
    ensures exponent == 0 ==> Pow(base, exponent) == 1
    ensures exponent > 0 ==> Pow(base, exponent) == base * Pow(base, exponent-1)
{
    if exponent == 0 then 1 else base * Pow(base, exponent-1)
}
// pure-end