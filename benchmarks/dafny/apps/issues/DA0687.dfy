// <vc-preamble>
predicate ValidInput(t: int, s: int, x: int)
{
    0 <= t <= 1000000000 && 2 <= s <= 1000000000 && 0 <= x <= 1000000000
}

predicate BarksAtTime(t: int, s: int, x: int)
    requires s > 0
{
    (x >= t && (x - t) % s == 0) || (x - 1 > t && (x - 1 - t) % s == 0)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(t: int, s: int, x: int) returns (result: string)
    requires ValidInput(t, s, x)
    ensures result == "YES" <==> BarksAtTime(t, s, x)
// </vc-spec>
// <vc-code>
{
    var f := false;

    if x - 1 > t && (x - 1 - t) % s == 0 {
        f := true;
    }

    if x >= t && (x - t) % s == 0 {
        f := true;
    }

    if f {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>
