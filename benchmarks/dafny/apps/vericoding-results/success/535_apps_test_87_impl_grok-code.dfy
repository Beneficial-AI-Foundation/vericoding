predicate ValidInput(m: int, d: int)
{
    1 <= m <= 12 && 1 <= d <= 7
}

function DaysInMonth(m: int): int
    requires 1 <= m <= 12
{
    [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][m-1]
}

function ColumnsNeeded(m: int, d: int): int
    requires ValidInput(m, d)
{
    1 + (d - 1 + DaysInMonth(m) - 1) / 7
}

// <vc-helpers>
lemma LemmaColumnsBound(m: int, d: int)
    requires ValidInput(m, d)
    ensures 4 <= ColumnsNeeded(m, d) <= 6
{
    // Proof by calculation of all possible cases
    var days := DaysInMonth(m);
    var k := d + days - 2;
    var res := 1 + k / 7;
    if m == 2 && d == 1 { assert k == 1 + 28 - 2 == 27; assert res == 1 + 3 == 4; }
    else if d == 7 && days >= 29 && m != 2 { assert k == 7 + days - 2; assert days <= 31; assert k <= 7 + 31 - 2 == 36; assert res <= 1 + 5 == 6; assert k >= 7 + 28 - 2 == 33; assert res >= 1 + 4 == 5; }
    else { assert k >= 1 + 28 - 2 == 27; assert res >= 4; assert k <= 7 + 31 - 2 == 36; assert res <= 6; }
}
// </vc-helpers>

// <vc-spec>
method solve(m: int, d: int) returns (result: int)
    requires ValidInput(m, d)
    ensures result == ColumnsNeeded(m, d)
    ensures 4 <= result <= 6
// </vc-spec>
// <vc-code>
{
    var days := DaysInMonth(m);
    result := 1 + (d - 1 + days - 1) / 7;
    LemmaColumnsBound(m, d);
}
// </vc-code>

