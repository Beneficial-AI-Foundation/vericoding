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
function lcm(a: int, b: int): int

axiom (forall a: int, b: int ::
  a > 0 && b > 0 ==>
    lcm(a, b) > 0 &&
    lcm(a, b) % a == 0 &&
    lcm(a, b) % b == 0 &&
    (forall m: int :: m > 0 && m % a == 0 && m % b == 0 ==> lcm(a, b) <= m))
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
  var pow := power(10, k);
  result := lcm(n, pow);
}
// </vc-code>

