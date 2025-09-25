// <vc-preamble>
predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 && |a| == n && forall i :: 0 <= i < |a| ==> a[i] >= 1
}

function Sum(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + Sum(s[1..])
}

predicate ValidSolution(a: seq<int>, b: seq<int>)
requires |a| == |b|
requires forall i :: 0 <= i < |a| ==> a[i] > 0
requires forall i :: 0 <= i < |b| ==> b[i] > 0
{
    |a| > 0 ==> forall i, j :: 0 <= i < |a| && 0 <= j < |a| ==> a[i] * b[i] == a[j] * b[j]
}
// </vc-preamble>

// <vc-helpers>
function gcd(x: int, y: int): int
requires x >= 0 && y >= 0
requires x > 0 || y > 0
decreases y
{
    if y == 0 then x else gcd(y, x % y)
}

lemma gcd_positive(x: int, y: int)
requires x >= 0 && y >= 0 && (x > 0 || y > 0)
ensures gcd(x, y) > 0
decreases y
{
    if y == 0 {
        assert gcd(x, y) == x;
        assert x > 0;
    } else {
        gcd_positive(y, x % y);
    }
}

lemma gcd_divides(x: int, y: int)
requires x >= 0 && y >= 0 && (x > 0 || y > 0)
ensures gcd(x, y) > 0
ensures x % gcd(x, y) == 0
ensures y % gcd(x, y) == 0
decreases y
{
    if y == 0 {
        assert gcd(x, y) == x;
        assert x > 0;
    } else {
        gcd_divides(y, x % y);
    }
}

function lcm(x: int, y: int): int
requires x > 0 && y > 0
ensures lcm(x, y) > 0
ensures lcm(x, y) % x == 0
ensures lcm(x, y) % y == 0
{
    gcd_divides(x, y);
    var g := gcd(x, y);
    var result := (x * y) / g;
    assert result == (x / g) * y;
    assert result == (y / g) * x;
    result
}

lemma lcm_divisible(x: int, y: int)
requires x > 0 && y > 0
ensures lcm(x, y) % x == 0
ensures lcm(x, y) % y == 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
requires ValidInput(n, a)
ensures 0 <= result < 1000000007
// </vc-spec>
// <vc-code>
{
    var mod := 1000000007;

    var current_lcm := a[0];
    var i := 1;
    while i < |a|
    invariant 1 <= i <= |a|
    invariant current_lcm > 0
    invariant forall j :: 0 <= j < i ==> current_lcm % a[j] == 0
    {
        current_lcm := lcm(current_lcm, a[i]);
        i := i + 1;
    }

    var sum := 0;
    i := 0;
    while i < |a|
    invariant 0 <= i <= |a|
    invariant sum >= 0
    {
        sum := sum + (current_lcm / a[i]);
        i := i + 1;
    }

    result := sum % mod;
}
// </vc-code>
