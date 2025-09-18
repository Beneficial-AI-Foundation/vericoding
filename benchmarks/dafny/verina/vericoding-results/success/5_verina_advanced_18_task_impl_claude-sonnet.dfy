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

// </vc-helpers>

// <vc-spec>
method IsArmstrong(n: nat) returns (result: bool)
    ensures 
        result == (n == SumPowers(n, CountDigits(n)))
// </vc-spec>
// <vc-code>
{
    var digits := CountDigits(n);
    var sum := SumPowers(n, digits);
    result := (n == sum);
}
// </vc-code>
