// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed gcd base cases */
predicate divides(a: int, b: int) {
    a != 0 && b % a == 0
}

function gcd(a: int, b: int): int
    requires a >= 0 && b >= 0
    ensures (a == 0 && b == 0) ==> (gcd(a, b) == 0)
    ensures (a > 0 || b > 0) ==> (gcd(a, b) > 0 && (a % gcd(a, b) == 0) && (b % gcd(a, b) == 0))
    ensures forall d | d > 0 && a % d == 0 && b % d == 0 :: d <= gcd(a,b)
    decreases a, b
{
    if a == 0 then b
    else if b == 0 then a
    else if a > b then gcd(a % b, b)
    else gcd(a, b % a)
}

function lcm(a: int, b: int): int
    requires a > 0 && b > 0
    ensures lcm(a, b) % a == 0
    ensures lcm(a, b) % b == 0
    ensures forall x :: x > 0 && x % a == 0 && x % b == 0 ==> lcm(a, b) <= x
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
/* code modified by LLM (iteration 4): Explicitly calling lcm function for clarity */
{
    var pK := power(10, k);
    result := lcm(n, pK);
}
// </vc-code>
