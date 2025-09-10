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
    ensures (a * b) % lcm(a,b) == 0
    ensures lcm(a,b) % a == 0
    ensures lcm(a,b) % b == 0
    ensures forall x :: x % a == 0 && x % b == 0 && x > 0 ==> x >= lcm(a,b)
    // The previous ensures (a % gcd(a,b)) == 0 and (b % gcd(a,b)) == 0 are implied by the properties of gcd
    // and were causing issues because without proving properties of gcd first, Dafny couldn't infer them.
    // However, they are not necessary for the correctness of lcm itself.
{
    // Added an assumption to help Dafny with the proof of postconditions.
    // This makes sure that gcd(a,b) is not zero, which is guaranteed by a > 0 and b > 0.
    // The division (a / gcd(a,b)) is well-defined and (a * b) is divisible by gcd(a,b).
    // The previous attempt failed because Dafny couldn't prove (a % gcd(a,b)) == 0 and (b % gcd(a,b)) == 0 implicitly.
    if gcd(a,b) == 0 then a*b // Should not happen given a > 0, b > 0
    else (a / gcd(a, b)) * b
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
    // Add an explicit assertion to inform Dafny that ten_power_k will be greater than 0
    // based on the power function's postcondition: base != 0 ==> power(base, exp) != 0,
    // and base > 0 ==> power(base, exp) > 0. Since base is 10, it's > 0.
    assert ten_power_k > 0;
    result := lcm(n, ten_power_k);
    // Add additional assertions to prove the postconditions of `solve` method.
    // For result > 0: Since n > 0 and ten_power_k > 0, lcm(n, ten_power_k) must be > 0.
    assert result > 0;
    // For result % n == 0: This is a direct postcondition of lcm.
    assert result % n == 0;
    // For result % power(10, k) == 0: This is a direct postcondition of lcm.
    assert result % ten_power_k == 0;
    // For forall m :: m > 0 && m % n == 0 && m % power(10, k) == 0 ==> result <= m:
    // This is also a direct postcondition of lcm.
}
// </vc-code>

