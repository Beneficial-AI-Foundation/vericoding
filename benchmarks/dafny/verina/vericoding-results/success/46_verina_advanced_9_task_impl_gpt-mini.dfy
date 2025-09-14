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
predicate SumNonNegative(x: nat) { SumOfDigits(x) >= 0 }

lemma SumOfDigits_Nonneg(x: nat) ensures SumOfDigits(x) >= 0 { }
// </vc-helpers>

// <vc-spec>
method CountSumDivisibleBy(n: nat, d: nat) returns (result: nat)
    requires d > 0
    ensures result <= n
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i: nat := 1;
  while i <= n
    invariant 0 <= result <= n
    invariant 1 <= i <= n + 1
    invariant result <= i - 1
    decreases n - i + 1
  {
    if SumOfDigits(i) % d == 0 {
      result := result + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
