function CountValidMinutes(a: int, b: int): int
    requires a >= 0 && b >= 0
    decreases a + b
{
    if a <= 0 || b <= 0 then 0
    else if a == 1 && b == 1 then 0
    else (if a > 1 || b > 1 then 1 else 0) + 
         CountValidMinutes(if a < b then a + 1 else a - 2, if a < b then b - 2 else b + 1)
}

// <vc-helpers>
lemma CountValidMinutesNonNegative(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures CountValidMinutes(a, b) >= 0
    decreases a + b
{
    if a <= 0 || b <= 0 {
        assert CountValidMinutes(a, b) == 0;
    } else if a == 1 && b == 1 {
        assert CountValidMinutes(a, b) == 0;
    } else {
        var next_a := if a < b then a + 1 else a - 2;
        var next_b := if a < b then b - 2 else b + 1;
        CountValidMinutesNonNegative(next_a, next_b);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(a1: int, a2: int) returns (result: int)
    requires a1 >= 1 && a2 >= 1
    ensures result >= 0
    ensures result == CountValidMinutes(a1, a2)
    ensures (a1 == 1 && a2 == 1) ==> result == 0
// </vc-spec>
// <vc-code>
{
    CountValidMinutesNonNegative(a1, a2);
    result := CountValidMinutesImpl(a1, a2);
}

function CountValidMinutesImpl(a: int, b: int): int
    requires a >= 0 && b >= 0
    ensures CountValidMinutesImpl(a, b) == CountValidMinutes(a, b)
    decreases a + b
{
    if a <= 0 || b <= 0 then 0
    else if a == 1 && b == 1 then 0
    else (if a > 1 || b > 1 then 1 else 0) + 
         CountValidMinutesImpl(if a < b then a + 1 else a - 2, if a < b then b - 2 else b + 1)
}
// </vc-code>

