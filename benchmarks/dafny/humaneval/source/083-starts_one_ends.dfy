method CountNumbersStartingOrEndingWithOne(n: nat) returns (count: nat)
    // pre-conditions-start
    requires n > 0
    // pre-conditions-end
    // post-conditions-start
    ensures n == 1 ==> count == 1
    ensures n > 1 ==> count == 18 * Pow(10, n - 2)
    // post-conditions-end
{
    // impl-start
    if n == 1 {
        count := 1;
    } else {
        count := 18 * Pow(10, n - 2);
    }
    // impl-end
}

function Pow(base: nat, exponent: nat): nat
    ensures exponent == 0 ==> Pow(base, exponent) == 1
    ensures exponent > 0 ==> Pow(base, exponent) == base * Pow(base, exponent-1)
{
    if exponent == 0 then 1 else base * Pow(base, exponent-1)
}
// pure-end
