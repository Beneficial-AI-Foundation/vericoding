// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method IsMonthWith30Days(month: int) returns (result: bool)
    requires 1 <= month <= 12
    ensures result <==> month == 4 || month == 6 || month == 9 || month == 11
// </vc-spec>
// </vc-spec>

// <vc-code>
method IsMonthWith30DaysImpl(month: int) returns (result: bool)
    requires 1 <= month <= 12
    ensures result <==> month == 4 || month == 6 || month == 9 || month == 11
{
    result := month == 4 || month == 6 || month == 9 || month == 11;
}
// </vc-code>
