// <vc-preamble>
function CountOneBits(n: nat) : nat
{
    if n == 0 then 0
    else (n % 2) + CountOneBits(n / 2)
}

function Power2(exp: nat) : nat
{
    if exp == 0 then 1
    else 2 * Power2(exp - 1)
}

predicate ValidInput(a: nat)
{
    a <= 1073741823
}

function ExpectedSolutions(a: nat) : nat
{
    Power2(CountOneBits(a))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SolveEquation(a: nat) returns (count: nat)
    requires ValidInput(a)
    ensures count == ExpectedSolutions(a)
// </vc-spec>
// <vc-code>
{
    var oneBits := CountOneBits(a);
    count := Power2(oneBits);
}
// </vc-code>
