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
lemma ColumnsNeeded_Properties(m: int, d: int)
    requires ValidInput(m, d)
    ensures 4 <= ColumnsNeeded(m, d) <= 6
{
    var daysInMonth := DaysInMonth(m);
    // Prove lower bound
    // Smallest daysInMonth is 28 (February)
    // Smallest d-1 is 0 (d=1)
    // Smallest (d-1 + daysInMonth - 1) is (0 + 28 - 1) = 27
    // Smallest 1 + (d-1 + daysInMonth - 1) / 7 is 1 + 27 / 7 = 1 + 3 = 4
    calc {
        1 + (d - 1 + daysInMonth - 1) / 7;
        {
            assert d - 1 >= 0;
            assert daysInMonth >= 28; // Smallest daysInMonth is for Feb
        }
        >= 1 + (0 + 28 - 1) / 7;
        == 1 + 27 / 7;
        == 1 + 3; // Integer division
        == 4;
    }

    // Prove upper bound
    // Largest daysInMonth is 31
    // Largest d-1 is 6 (d=7)
    // Largest (d-1 + daysInMonth - 1) is (6 + 31 - 1) = 36
    // Largest 1 + (d-1 + daysInMonth - 1) / 7 is 1 + 5 = 6
    calc {
        1 + (d - 1 + daysInMonth - 1) / 7;
        {
            assert d - 1 <= 6;
            assert daysInMonth <= 31; // Largest daysInMonth
        }
        <= 1 + (6 + 31 - 1) / 7;
        == 1 + 36 / 7;
        == 1 + 5; // Integer division
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
    var dim := DaysInMonth(m);
    result := 1 + (d - 1 + dim - 1) / 7;
    ColumnsNeeded_Properties(m, d); // Prove the postcondition `4 <= result <= 6`
}
// </vc-code>

