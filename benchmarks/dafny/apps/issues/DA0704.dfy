// <vc-preamble>
predicate ValidInput(cnt_1: int, cnt_2: int, x: int, y: int)
{
    cnt_1 >= 1 && cnt_1 < 1000000000 &&
    cnt_2 >= 1 && cnt_2 < 1000000000 &&
    cnt_1 + cnt_2 <= 1000000000 &&
    x >= 2 && y >= 2 && x < y &&
    x <= 30000 && y <= 30000
}

function f(m: int, n: int, x: int, y: int): int
    requires x > 0 && y > 0
{
    var temp := m / y - m / (x * y);
    if n - temp > 0 then n - temp else 0
}

function CountNotDivisibleByBoth(v: int, x: int, y: int): int
    requires x > 0 && y > 0
{
    v - v / x - v / y + v / (x * y)
}

predicate CanSelect(v: int, cnt_1: int, cnt_2: int, x: int, y: int)
    requires x > 0 && y > 0
{
    f(v, cnt_1, x, y) + f(v, cnt_2, y, x) <= CountNotDivisibleByBoth(v, x, y)
}

predicate IsMinimal(v: int, cnt_1: int, cnt_2: int, x: int, y: int)
    requires x > 0 && y > 0
{
    v > 0 && 
    CanSelect(v, cnt_1, cnt_2, x, y) &&
    (v == 1 || !CanSelect(v - 1, cnt_1, cnt_2, x, y))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(cnt_1: int, cnt_2: int, x: int, y: int) returns (result: int)
    requires ValidInput(cnt_1, cnt_2, x, y)
    ensures result > 0
    ensures result <= x * y * (cnt_1 + cnt_2)
    ensures IsMinimal(result, cnt_1, cnt_2, x, y)
// </vc-spec>
// <vc-code>
{
    var lo: int := 0;
    var hi: int := x * y * (cnt_1 + cnt_2);

    while lo < hi
        invariant 0 <= lo <= hi <= x * y * (cnt_1 + cnt_2)
        invariant hi > 0
        invariant CanSelect(hi, cnt_1, cnt_2, x, y)
        invariant lo == 0 || !CanSelect(lo, cnt_1, cnt_2, x, y)
        decreases hi - lo
    {
        var mid: int := lo + (hi - lo) / 2;

        var f1: int := f(mid, cnt_1, x, y);
        var f2: int := f(mid, cnt_2, y, x);
        var available: int := CountNotDivisibleByBoth(mid, x, y);

        if f1 + f2 <= available {
            hi := mid;
        } else {
            lo := mid + 1;
        }
    }

    result := hi;
}
// </vc-code>
