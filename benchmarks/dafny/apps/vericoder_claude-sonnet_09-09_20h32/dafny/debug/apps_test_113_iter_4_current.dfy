function power(base: int, exp: int): int
    requires exp >= 0
    ensures exp == 0 ==> power(base, exp) == 1
    ensures base > 0 ==> power(base, exp) > 0
    ensures base != 0 ==> power(base, exp) != 0
    decreases exp
{
    if exp == 0 then 1
    else base * power(base, exp - 1)
}

// <vc-helpers>
function gcd(a: int, b: int): int
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
    ensures a % gcd(a, b) == 0
    ensures b % gcd(a, b) == 0
    decreases if a > b then a else b
{
    if a == b then a
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
}

function lcm(a: int, b: int): int
    requires a > 0 && b > 0
    ensures lcm(a, b) > 0
    ensures lcm(a, b) % a == 0
    ensures lcm(a, b) % b == 0
{
    (a * b) / gcd(a, b)
}

lemma lcm_is_minimal(a: int, b: int, m: int)
    requires a > 0 && b > 0
    requires m > 0 && m % a == 0 && m % b == 0
    ensures lcm(a, b) <= m
{
}

lemma power_10_positive(k: int)
    requires k >= 0
    ensures power(10, k) > 0
{
}

lemma lcm_minimal_property(a: int, b: int, m: int)
    requires a > 0 && b > 0
    requires m > 0 && m % a == 0 && m % b == 0
    ensures lcm(a, b) <= m
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires n > 0 && k >= 0
    ensures result > 0
    ensures result % n == 0
    ensures result % power(10, k) == 0
    ensures forall m :: m > 0 && m % n == 0 && m % power(10, k) == 0 ==> result <= m
// </vc-spec>
// <vc-code>
{
    var pow10k := power(10, k);
    power_10_positive(k);
    result := lcm(n, pow10k);
    lcm_minimal_property(n, pow10k, result);
}
// </vc-code>

