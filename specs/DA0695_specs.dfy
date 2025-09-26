// <vc-preamble>
predicate ValidInput(x: int, k: int) {
    x >= 0 && k >= 0
}

predicate ValidOutput(result: int) {
    result >= 0 && result < 1000000007
}

function MOD(): int { 1000000007 }
// </vc-preamble>

// <vc-helpers>
function ModPow(base: int, exp: int, mod: int): int
    requires mod > 0
    requires exp >= 0
    ensures ModPow(base, exp, mod) >= 0
    ensures ModPow(base, exp, mod) < mod
{
    if exp == 0 then
        1 % mod
    else if exp == 1 then
        base % mod
    else if exp % 2 == 0 then
        var half := ModPow(base, exp / 2, mod);
        (half * half) % mod
    else
        var half := ModPow(base, exp / 2, mod);
        (((half * half) % mod) * (base % mod)) % mod
}
// </vc-helpers>

// <vc-spec>
// </vc-spec>
// <vc-code>
// </vc-code>
