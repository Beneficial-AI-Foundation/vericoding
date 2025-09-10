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
lemma power_positive(base: int, exp: int)
    requires exp >= 0 && base > 0
    ensures power(base, exp) > 0
{
    if exp == 0 {
        calc {
            power(base, exp);
            1;
            > 0;
        }
    } else {
        power_positive(base, exp - 1);
        calc {
            power(base, exp);
            base * power(base, exp - 1);
        }
    }
}

lemma power_nonzero(base: int, exp: int)
    requires exp >= 0 && base != 0
    ensures power(base, exp) != 0
{
    if exp == 0 {
        calc {
            power(base, exp);
            1;
            != 0;
        }
    } else {
        power_nonzero(base, exp - 1);
        calc {
            power(base, exp);
            base * power(base, exp - 1);
        }
    }
}

function lcm(a: int, b: int): int
    requires a > 0 && b > 0
    ensures a > 0 && b > 0 ==> lcm(a, b) > 0
    ensures lcm(a, b) % a == 0
    ensures lcm(a, b) % b == 0
    ensures forall m :: m > 0 && m % a == 0 && m % b == 0 ==> lcm(a, b) <= m
{
    a * b / gcd(a, b)
}

function gcd(a: int, b: int): int
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
    ensures a % gcd(a, b) == 0
    ensures b % gcd(a, b) == 0
    ensures forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= gcd(a, b)
{
    if b == 0 then a else gcd(b, a % b)
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
    result := lcm(n, power(10, k));
}
// </vc-code>

