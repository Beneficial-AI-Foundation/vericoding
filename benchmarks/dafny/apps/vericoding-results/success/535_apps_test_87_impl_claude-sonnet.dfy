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
lemma ColumnsNeededBounds(m: int, d: int)
    requires ValidInput(m, d)
    ensures 4 <= ColumnsNeeded(m, d) <= 6
{
    var days := DaysInMonth(m);
    var cols := 1 + (d - 1 + days - 1) / 7;
    
    // Min case: d = 1, days = 28 (February)
    // cols = 1 + (1 - 1 + 28 - 1) / 7 = 1 + 27 / 7 = 1 + 3 = 4
    
    // Max case: d = 7, days = 31
    // cols = 1 + (7 - 1 + 31 - 1) / 7 = 1 + 36 / 7 = 1 + 5 = 6
    
    assert days >= 28 && days <= 31;
    assert d >= 1 && d <= 7;
    assert d - 1 + days - 1 >= 27 && d - 1 + days - 1 <= 36;
    assert (d - 1 + days - 1) / 7 >= 3 && (d - 1 + days - 1) / 7 <= 5;
    assert cols >= 4 && cols <= 6;
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
    result := 1 + (d - 1 + DaysInMonth(m) - 1) / 7;
    ColumnsNeededBounds(m, d);
}
// </vc-code>

