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
    requires a >= 0 && b >= 0
    decreases b, a
{
    if b == 0 then a
    else gcd(b, a % b)
}

function lcm(a: int, b: int): int
    requires a > 0 && b > 0
    ensures (a % gcd(a,b)) == 0
    ensures (b % gcd(a,b)) == 0
    ensures (a * b) % lcm(a,b) == 0
    ensures lcm(a,b) % a == 0
    ensures lcm(a,b) % b == 0
    ensures forall x :: x % a == 0 && x % b == 0 && x > 0 ==> x >= lcm(a,b)
{
    (a / gcd(a, b)) * b
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
    var ten_power_k := power(10, k);
    result := lcm(n, ten_power_k);
}
// </vc-code>

