// <vc-preamble>
function SumOfDigits(x: nat): nat
    decreases x
{
    if x == 0 then 0 else (x % 10) + SumOfDigits(x / 10)
}

predicate IsSumDivisibleBy(x: nat, d: nat)
    requires d > 0
{
    (SumOfDigits(x) % d) == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
// </vc-helpers>

// <vc-spec>
method CountSumDivisibleBy(n: nat, d: nat) returns (result: nat)
    requires d > 0
    ensures result <= n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implemented simple counting loop with correct invariant to prove postcondition */
{
  result := 0;
  var i: int := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant 0 <= result <= i - 1
  {
    if IsSumDivisibleBy(i, d) {
      result := result + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
