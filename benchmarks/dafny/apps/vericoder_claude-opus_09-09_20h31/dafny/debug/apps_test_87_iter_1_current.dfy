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
    assert days == [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][m-1];
    assert 28 <= days <= 31;
    
    var numerator := d - 1 + days - 1;
    assert numerator == d + days - 2;
    
    // When d = 1 and days = 28: numerator = 1 + 28 - 2 = 27
    // When d = 7 and days = 31: numerator = 7 + 31 - 2 = 36
    assert 27 <= numerator <= 36;
    
    // 27 / 7 = 3, so 1 + 27/7 = 4
    // 36 / 7 = 5, so 1 + 36/7 = 6
    assert 27 / 7 == 3;
    assert 36 / 7 == 5;
    
    var result := 1 + numerator / 7;
    assert 4 <= result <= 6;
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
    ColumnsNeededBounds(m, d);
    result := 1 + (d - 1 + DaysInMonth(m) - 1) / 7;
}
// </vc-code>

