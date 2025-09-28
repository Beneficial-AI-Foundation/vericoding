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
function CountDigitsHelper(n: nat, count: nat): nat
    decreases n
    ensures CountDigitsHelper(n, count) == count + CountDigits(n)
{
    if n == 0 then
        count + 1
    else if n < 10 then
        count + 1
    else
        CountDigitsHelper(n / 10, count + 1)
}

lemma SumPowersLemma(n: nat, k: nat, acc: nat)
    decreases n
    ensures acc + SumPowers(n, k) == SumPowers(n, k) + acc
{
}

function ComputeSum(n: nat, k: nat, sum: nat): nat
    decreases n
    ensures ComputeSum(n, k, sum) == sum + SumPowers(n, k)
{
    if n == 0 then
        sum
    else
        ComputeSum(n / 10, k, sum + PowNat(n % 10, k))
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
    var totalSum := ComputeSum(n, digitCount, 0);
    result := n == totalSum;
}
// </vc-code>
