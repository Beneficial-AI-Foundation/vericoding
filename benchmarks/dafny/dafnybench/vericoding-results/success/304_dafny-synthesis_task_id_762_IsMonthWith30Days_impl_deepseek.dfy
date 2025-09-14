

// <vc-helpers>
lemma Month30Lemma(month: int)
    requires 1 <= month <= 12
    ensures month == 4 || month == 6 || month == 9 || month == 11 <==> month in {4,6,9,11}
{
}
// </vc-helpers>

// <vc-spec>
method IsMonthWith30Days(month: int) returns (result: bool)
    requires 1 <= month <= 12
    ensures result <==> month == 4 || month == 6 || month == 9 || month == 11
// </vc-spec>
// <vc-code>
{
    Month30Lemma(month);
    return month == 4 || month == 6 || month == 9 || month == 11;
}
// </vc-code>

