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
    assert DaysInMonth(m) >= 28;
    assert DaysInMonth(m) <= 31;
    var expr := d - 1 + DaysInMonth(m) - 1;
    assert expr >= 27;
    assert expr <= 36;
    calc {
        ColumnsNeeded(m, d);
        == 1 + expr / 7;
        >= 1 + 27 / 7;
        == 1 + 3;
        == 4;
    }
    calc {
        ColumnsNeeded(m, d);
        == 1 + expr / 7;
        <= 1 + 36 / 7;
        == 1 + 5;
        == 6;
    }
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
    result := ColumnsNeeded(m, d);
}
// </vc-code>

