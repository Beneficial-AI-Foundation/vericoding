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
lemma LCM_NonZero(a: int, b: int)
    requires a > 0 && b > 0
    ensures lcm(a, b) > 0
{
}

lemma LCM_Divides(a: int, b: int)
    requires a > 0 && b > 0
    ensures a % lcm(a, b) == 0 && b % lcm(a, b) == 0
{
}

lemma LCM_IsMultiple(a: int, b: int)
    requires a > 0 && b > 0
    ensures forall m :: m > 0 && m % a == 0 && m % b == 0 ==> lcm(a, b) <= m
{
}

lemma Power10_Positive(k: int)
    requires k >= 0
    ensures power(10, k) > 0
{
    if k > 0 {
        Power10_Positive(k - 1);
    }
}

function lcm(a: int, b: int): int
    requires a > 0 && b > 0
    ensures lcm(a, b) > 0
    ensures a % lcm(a, b) == 0 && b % lcm(a, b) == 0
    ensures forall m :: m > 0 && m % a == 0 && m % b == 0 ==> lcm(a, b) <= m
{
    a * b / gcd(a, b)
}

function gcd(a: int, b: int): int
    requires a > 0 && b > 0
    decreases a, b
{
    if a == b then
        a
    else if a > b then
        gcd(a - b, b)
    else
        gcd(a, b - a)
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
    var p10 := power(10, k);
    Power10_Positive(k);
    result := lcm(n, p10);
    LCM_NonZero(n, p10);
    LCM_Divides(n, p10);
    LCM_IsMultiple(n, p10);
}
// </vc-code>

