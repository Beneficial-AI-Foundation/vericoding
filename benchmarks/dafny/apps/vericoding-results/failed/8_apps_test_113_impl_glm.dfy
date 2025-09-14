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
    decreases b
{
    if b == 0 then a
    else gcd(b, a % b)
}

lemma gcd_property(x: int, y: int)
    requires x >= 0 && y > 0
    ensures gcd(x, y) == gcd(y, x % y)
{
}

lemma powerpositive(base: int, exp: int)
    requires exp >= 0
    ensures base > 0 ==> power(base, exp) > 0
    decreases exp
{
    if exp == 0 {
    } else {
        powerpositive(base, exp - 1);
    }
}

lemma power10nonzero(k: int)
    requires k >= 0
    ensures power(10, k) != 0
    decreases k
{
    if k == 0 {
    } else {
        power10nonzero(k - 1);
    }
}

lemma lcmexists(n: int, k: int) returns (result: int)
    requires n > 0 && k >= 0
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
function gcd(a: int, b: int): int
    requires a >= 0 && b >= 0
    decreases b
{
    if b == 0 then a
    else gcd(b, a % b)
}

lemma gcd_property(x: int, y: int)
    requires x >= 0 && y > 0
    ensures gcd(x, y) == gcd(y, x % y)
{
}

lemma powerpositive(base: int, exp: int)
    requires exp >= 0
    ensures base > 0 ==> power(base, exp) > 0
    decreases exp
{
    if exp == 0 {
    } else {
        powerpositive(base, exp - 1);
    }
}

lemma power10nonzero(k: int)
    requires k >= 0
    ensures power(10, k) != 0
    decreases k
{
    if k == 0 {
    } else {
        power10nonzero(k - 1);
    }
}

lemma lcmexists(n: int, k: int) returns (result: int)
    requires n > 0 && k >= 0
// </vc-code>

