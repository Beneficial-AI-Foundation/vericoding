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
function BoolToNat(b: bool): nat { if b then 1 else 0 }
// </vc-helpers>

// <vc-spec>
method CountSumDivisibleBy(n: nat, d: nat) returns (result: nat)
    requires d > 0
    ensures result <= n
// </vc-spec>
// <vc-code>
{
  var i: nat := 1;
  result := 0;
  while i <= n
    invariant i >= 1
    invariant i <= n + 1
    invariant result <= i - 1
    invariant d > 0
    decreases n - i + 1
  {
    if IsSumDivisibleBy(i, d) {
      result := result + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
