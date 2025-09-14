// <vc-preamble>
function CountDigits(n: nat): nat
    decreases n
{
    if n == 0 then 1 else if n < 10 then 1 else 1 + CountDigits(n / 10)
}

function PowNat(base: nat, exp: nat): nat
    decreases exp
{
    if exp == 0 then 
        1 
    else 
        base * PowNat(base, exp - 1)
}

function SumPowers(n: nat, k: nat): nat
    decreases n
{
    if n == 0 then 0 else PowNat(n % 10, k) + SumPowers(n / 10, k)
}
// </vc-preamble>

// <vc-helpers>
function DigitCountIsValid(n: nat): bool
    decreases n
{
    n >= 0
}

lemma DigitCountLemma(n: nat)
    ensures CountDigits(n) > 0
    decreases n
{
    if n == 0 {
    } else if n < 10 {
    } else {
        DigitCountLemma(n / 10);
    }
}

lemma SumPowersLemma(n: nat, k: nat)
    requires k > 0
    decreases n
    ensures SumPowers(n, k) >= 0
{
    if n == 0 {
    } else {
        SumPowersLemma(n / 10, k);
    }
}
// </vc-helpers>

// <vc-spec>
method IsArmstrong(n: nat) returns (result: bool)
    ensures 
        result == (n == SumPowers(n, CountDigits(n)))
// </vc-spec>
// <vc-code>
{
    var digitCount := CountDigits(n);
    var sum := SumPowers(n, digitCount);
    result := n == sum;
}
// </vc-code>
