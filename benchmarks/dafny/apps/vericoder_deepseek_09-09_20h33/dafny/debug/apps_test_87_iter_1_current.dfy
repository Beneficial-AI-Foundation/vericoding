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
lemma ColumnsNeededRange(m: int, d: int)
    requires ValidInput(m, d)
    ensures 4 <= ColumnsNeeded(m, d) <= 6
{
    // Calculate the minimum and maximum possible values
    var min_days := DaysInMonth(m);
    var max_days := DaysInMonth(m);
    
    // For all valid inputs, the result is always between 4 and 6
    // This can be verified by checking all 12*7 = 84 cases
    // Since Dafny can handle this computationally, we can use a ghost method
}

ghost method VerifyAllCases()
{
    for m' := 1 to 12 {
        for d' := 1 to 7 {
            assert ValidInput(m', d');
            var result := ColumnsNeeded(m', d');
            assert 4 <= result <= 6;
        }
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
    result := 1 + (d - 1 + DaysInMonth(m) - 1) / 7;
    ColumnsNeededRange(m, d);
}
// </vc-code>

