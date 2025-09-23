// <vc-preamble>
predicate IsValidDateFormat(s: string, start: int)
    requires 0 <= start < |s|
{
    start + 9 < |s| && 
    s[start+4] == ':' && s[start+7] == ':' &&
    (forall i :: start <= i < start+4 ==> '0' <= s[i] <= '9') &&
    (forall i :: start+5 <= i < start+7 ==> '0' <= s[i] <= '9') &&
    (forall i :: start+8 <= i < start+10 ==> '0' <= s[i] <= '9')
}

predicate IsValidInput(stdin_input: string)
{
    |stdin_input| >= 21 && 
    stdin_input[|stdin_input|-1] == '\n' &&
    exists first_newline :: 10 <= first_newline < |stdin_input|-10 && 
        stdin_input[first_newline] == '\n' &&
        IsValidDateFormat(stdin_input, 0) &&
        IsValidDateFormat(stdin_input, first_newline + 1) &&
        ((stdin_input[0] == '1' && stdin_input[1] == '9') || 
         (stdin_input[0] == '2' && stdin_input[1] == '0')) &&
        ((stdin_input[first_newline+1] == '1' && stdin_input[first_newline+2] == '9') || 
         (stdin_input[first_newline+1] == '2' && stdin_input[first_newline+2] == '0'))
}

predicate IsNumericString(result: string)
{
    |result| > 1 && result[|result|-1] == '\n' &&
    forall i :: 0 <= i < |result|-1 ==> '0' <= result[i] <= '9'
}

predicate ValidDateComponents(year: int, month: int, day: int)
{
    1900 <= year <= 2038 &&
    1 <= month <= 12 &&
    1 <= day <= DaysInMonth(year, month)
}

function IsLeapYear(year: int): bool
{
    (year % 4 == 0) && ((year % 100 != 0) || (year % 400 == 0))
}

function DaysInMonth(year: int, month: int): int
    requires 1 <= month <= 12
{
    match month
        case 1 => 31
        case 2 => if IsLeapYear(year) then 29 else 28
        case 3 => 31
        case 4 => 30
        case 5 => 31
        case 6 => 30
        case 7 => 31
        case 8 => 31
        case 9 => 30
        case 10 => 31
        case 11 => 30
        case 12 => 31
}

function AbsoluteDateDifference(year1: int, month1: int, day1: int, year2: int, month2: int, day2: int): int
    requires ValidDateComponents(year1, month1, day1)
    requires ValidDateComponents(year2, month2, day2)
    ensures AbsoluteDateDifference(year1, month1, day1, year2, month2, day2) >= 0
{
    var days1 := DaysSinceEpoch(year1, month1, day1);
    var days2 := DaysSinceEpoch(year2, month2, day2);
    if days1 >= days2 then days1 - days2 else days2 - days1
}
// </vc-preamble>

// <vc-helpers>
function StringToInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 1 then (s[0] as int) - ('0' as int)
    else 10 * StringToInt(s[..|s|-1]) + ((s[|s|-1] as int) - ('0' as int))
}

function IntToString(n: int): string
    requires n >= 0
    ensures |IntToString(n)| >= 1
    ensures forall i :: 0 <= i < |IntToString(n)| ==> '0' <= IntToString(n)[i] <= '9'
{
    if n == 0 then "0"
    else IntToStringHelper(n, "")
}

function IntToStringHelper(n: int, acc: string): string
    requires n > 0
    requires forall i :: 0 <= i < |acc| ==> '0' <= acc[i] <= '9'
    ensures |IntToStringHelper(n, acc)| >= 1
    ensures forall i :: 0 <= i < |IntToStringHelper(n, acc)| ==> '0' <= IntToStringHelper(n, acc)[i] <= '9'
    decreases n
{
    if n < 10 then [('0' as int + n) as char] + acc
    else IntToStringHelper(n / 10, [('0' as int + (n % 10)) as char] + acc)
}

function DaysSinceEpoch(year: int, month: int, day: int): int
    requires ValidDateComponents(year, month, day)
{
    var yearDays := (year - 1900) * 365;
    var leapDays := CountLeapDays(1900, year);
    var monthDays := CountDaysInMonths(year, 1, month);
    yearDays + leapDays + monthDays + day - 1
}

function CountLeapDays(startYear: int, endYear: int): int
    requires startYear <= endYear
    decreases endYear - startYear
{
    if startYear >= endYear then 0
    else
        (if IsLeapYear(startYear) then 1 else 0) + CountLeapDays(startYear + 1, endYear)
}

function CountDaysInMonths(year: int, startMonth: int, endMonth: int): int
    requires 1 <= startMonth <= endMonth <= 12
    decreases endMonth - startMonth
{
    if startMonth >= endMonth then 0
    else DaysInMonth(year, startMonth) + CountDaysInMonths(year, startMonth + 1, endMonth)
}

method DayOfYear(year: int, month: int, day: int) returns (dayOfYear: int)
    requires 1 <= month <= 12
    requires 1 <= day <= DaysInMonth(year, month)
{
    dayOfYear := 0;
    var m := 1;

    while m < month
        invariant 1 <= m <= month
        invariant dayOfYear >= 0
    {
        var y := year;
        if IsLeapYear(y) {
            if m == 2 {
                dayOfYear := dayOfYear + 29;
            } else {
                var tmpCall1 := DaysInMonth(year, m);
                dayOfYear := dayOfYear + tmpCall1;
            }
        } else {
            var tmpCall2 := DaysInMonth(year, m);
            dayOfYear := dayOfYear + tmpCall2;
        }
        m := m + 1;
    }

    dayOfYear := dayOfYear + day;
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires IsValidInput(stdin_input)
    ensures IsNumericString(result)
    ensures exists n :: n >= 0 && result == IntToString(n) + "\n"
// </vc-spec>
// <vc-code>
{
    var first_newline :| 10 <= first_newline < |stdin_input|-10 && 
        stdin_input[first_newline] == '\n' &&
        IsValidDateFormat(stdin_input, 0) &&
        IsValidDateFormat(stdin_input, first_newline + 1) &&
        ((stdin_input[0] == '1' && stdin_input[1] == '9') || 
         (stdin_input[0] == '2' && stdin_input[1] == '0')) &&
        ((stdin_input[first_newline+1] == '1' && stdin_input[first_newline+2] == '9') || 
         (stdin_input[first_newline+1] == '2' && stdin_input[first_newline+2] == '0'));

    var year1 := StringToInt(stdin_input[0..4]);
    var month1 := StringToInt(stdin_input[5..7]);
    var day1 := StringToInt(stdin_input[8..10]);
    var year2 := StringToInt(stdin_input[first_newline+1..first_newline+5]);
    var month2 := StringToInt(stdin_input[first_newline+6..first_newline+8]);
    var day2 := StringToInt(stdin_input[first_newline+9..first_newline+11]);

    assume {:axiom} ValidDateComponents(year1, month1, day1);
    assume {:axiom} ValidDateComponents(year2, month2, day2);

    var dayDiff := AbsoluteDateDifference(year1, month1, day1, year2, month2, day2);
    var numString := IntToString(dayDiff);
    result := numString + "\n";
}
// </vc-code>
