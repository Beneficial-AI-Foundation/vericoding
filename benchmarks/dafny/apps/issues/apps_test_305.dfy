// <vc-preamble>
predicate ValidInput(a: int, b: int, c: int, d: int, e: int, f: int)
{
    a >= 1 && a <= 100000 &&
    b >= 1 && b <= 100000 &&
    c >= 1 && c <= 100000 &&
    d >= 1 && d <= 100000 &&
    e >= 1 && e <= 1000 &&
    f >= 1 && f <= 1000
}

function MaxType1Suits(ties: int, jackets: int): int
    requires ties >= 0 && jackets >= 0
{
    if ties <= jackets then ties else jackets
}

function MaxType2Suits(jackets: int, scarves: int, vests: int): int
    requires jackets >= 0 && scarves >= 0 && vests >= 0
{
    var min_scarves_vests := if scarves <= vests then scarves else vests;
    if jackets <= min_scarves_vests then jackets else min_scarves_vests
}

function OptimalRevenue(a: int, b: int, c: int, d: int, e: int, f: int): int
    requires a >= 0 && b >= 0 && c >= 0 && d >= 0 && e >= 0 && f >= 0
{
    if e >= f then
        var suits1 := MaxType1Suits(a, d);
        var remaining_jackets := d - suits1;
        var suits2 := MaxType2Suits(remaining_jackets, b, c);
        suits1 * e + suits2 * f
    else
        var suits2 := MaxType2Suits(d, b, c);
        var remaining_jackets := d - suits2;
        var suits1 := MaxType1Suits(a, remaining_jackets);
        suits2 * f + suits1 * e
}
// </vc-preamble>

// <vc-helpers>
function min2(x: int, y: int): int
{
    if x <= y then x else y
}

function min3(x: int, y: int, z: int): int
{
    min2(min2(x, y), z)
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, d: int, e: int, f: int) returns (result: int)
    requires ValidInput(a, b, c, d, e, f)
    ensures result == OptimalRevenue(a, b, c, d, e, f)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var ans: int;
    var remaining_d: int := d;
    var remaining_a: int := a;

    if e >= f {
        ans := min2(a, d);
        remaining_d := d - ans;
        remaining_a := a - ans;
        ans := ans * e;
        var tmpCall1 := min3(remaining_d, b, c);
        ans := ans + tmpCall1 * f;
    } else {
        ans := min3(d, b, c);
        remaining_d := d - ans;
        ans := ans * f;
        var tmpCall2 := min2(remaining_a, remaining_d);
        ans := ans + tmpCall2 * e;
    }

    result := ans;
}
// </vc-code>
