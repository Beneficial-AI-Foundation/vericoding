// <vc-preamble>
predicate ValidInput(n: int, a: int, b: int) {
    2 <= n <= 1000000000 &&
    1 <= a < b <= n &&
    b <= 200000
}

function MOD(): int { 1000000007 }

function PowerMod(base: int, exp: int, mod: int): int
    requires base >= 0 && exp >= 0 && mod > 0
    ensures 0 <= PowerMod(base, exp, mod) < mod
    decreases exp
{
    if exp == 0 then 1 % mod
    else if exp % 2 == 0 then 
        PowerMod((base * base) % mod, exp / 2, mod)
    else 
        (base * PowerMod(base, exp - 1, mod)) % mod
}

function ModInverse(a: int, mod: int): int
    requires mod > 1 && a > 0
    ensures 0 <= ModInverse(a, mod) < mod
{
    PowerMod(a, mod - 2, mod)
}

function BinomialHelper(n: int, k: int, i: int, numerator: int, denominator: int, mod: int): int
    requires n >= 0 && k >= 0 && 0 <= i <= k && mod > 1
    requires numerator >= 0 && denominator > 0
    requires k <= 200000 // Bound k to ensure no overflow issues
    ensures 0 <= BinomialHelper(n, k, i, numerator, denominator, mod) < mod
    decreases k - i
{
    if i >= k then
        (numerator * ModInverse(denominator, mod)) % mod
    else
        var new_numerator := (numerator * (n - i)) % mod;
        var factor := i + 1;
        var new_denominator := if (denominator * factor) % mod == 0 then 1 else (denominator * factor) % mod;
        BinomialHelper(n, k, i + 1, new_numerator, new_denominator, mod)
}

function BinomialMod(n: int, k: int, mod: int): int
    requires n >= 0 && k >= 0 && mod > 1
    requires k <= 200000 // Add bound to prevent overflow
    ensures 0 <= BinomialMod(n, k, mod) < mod
{
    if k > n then 0
    else if k == 0 || k == n then 1
    else if k > n - k then BinomialMod(n, n - k, mod)
    else
        BinomialHelper(n, k, 0, 1, 1, mod)
}

function CalculateValidBouquets(n: int, a: int, b: int): int
    requires ValidInput(n, a, b)
    ensures 0 <= CalculateValidBouquets(n, a, b) < MOD()
{
    var mod := MOD();
    var total_ways := PowerMod(2, n, mod);
    var ways_with_a := BinomialMod(n, a, mod);
    var ways_with_b := BinomialMod(n, b, mod);
    var result := (total_ways - 1 - ways_with_a - ways_with_b) % mod;
    if result < 0 then result + mod else result
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountValidBouquets(n: int, a: int, b: int) returns (result: int)
    requires ValidInput(n, a, b)
    ensures result == CalculateValidBouquets(n, a, b)
    ensures 0 <= result < MOD()
// </vc-spec>
// <vc-code>
{
    var mod := MOD();
    var total_ways := PowerMod(2, n, mod);
    var ways_with_a := BinomialMod(n, a, mod);
    var ways_with_b := BinomialMod(n, b, mod);
    
    result := (total_ways - 1 - ways_with_a - ways_with_b) % mod;
    if result < 0 {
        result := result + mod;
    }
}
// </vc-code>
