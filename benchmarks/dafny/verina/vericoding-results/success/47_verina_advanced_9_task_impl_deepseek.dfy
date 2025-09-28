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
lemma SumModLemma(x: nat, d: nat)
    requires d > 0
    ensures (SumOfDigits(x) % d == 0) == IsSumDivisibleBy(x, d)
{
}

function CountUpTo(n: nat, d: nat): nat
    requires d > 0
    ensures CountUpTo(n, d) <= n
    decreases n
{
    if n == 0 then 0 else
    (if IsSumDivisibleBy(n, d) then 1 else 0) + CountUpTo(n - 1, d)
}
// </vc-helpers>

// <vc-spec>
method CountSumDivisibleBy(n: nat, d: nat) returns (result: nat)
    requires d > 0
    ensures result <= n
// </vc-spec>
// <vc-code>
{
    result := CountUpTo(n, d);
}
// </vc-code>
