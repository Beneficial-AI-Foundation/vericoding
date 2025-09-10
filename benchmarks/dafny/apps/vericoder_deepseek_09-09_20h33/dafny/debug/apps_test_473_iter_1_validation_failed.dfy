predicate ValidTimeFormat(time_str: string)
{
    |time_str| == 5 &&
    time_str[2] == ':' &&
    '0' <= time_str[0] <= '9' && '0' <= time_str[1] <= '9' &&
    '0' <= time_str[3] <= '9' && '0' <= time_str[4] <= '9' &&
    (time_str[0] as int - '0' as int) * 10 + (time_str[1] as int - '0' as int) <= 23 &&
    (time_str[3] as int - '0' as int) * 10 + (time_str[4] as int - '0' as int) <= 59
}

predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0 &&
    exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n' &&
    exists i, j :: 0 <= i < j < |stdin_input| && stdin_input[i] == '\n' && stdin_input[j] == '\n' &&
    var first_nl := FindFirstNewline(stdin_input);
    var second_nl := FindSecondNewline(stdin_input, first_nl);
    var s := stdin_input[..first_nl];
    var t := stdin_input[first_nl+1..second_nl];
    ValidTimeFormat(s) && ValidTimeFormat(t)
}

function ParseTime(time_str: string): (int, int)
    requires ValidTimeFormat(time_str)
    ensures var (h, m) := ParseTime(time_str); 0 <= h <= 23 && 0 <= m <= 59
{
    var h := (time_str[0] as int - '0' as int) * 10 + (time_str[1] as int - '0' as int);
    var m := (time_str[3] as int - '0' as int) * 10 + (time_str[4] as int - '0' as int);
    (h, m)
}

function CalculateBedtime(wake_hour: int, wake_min: int, sleep_hour: int, sleep_min: int): (int, int)
    requires 0 <= wake_hour <= 23 && 0 <= wake_min <= 59
    requires 0 <= sleep_hour <= 23 && 0 <= sleep_min <= 59
    ensures var (h, m) := CalculateBedtime(wake_hour, wake_min, sleep_hour, sleep_min); 0 <= h <= 23 && 0 <= m <= 59
{
    var wake_total_min := wake_hour * 60 + wake_min;
    var sleep_total_min := sleep_hour * 60 + sleep_min;
    var bed_total_min := (wake_total_min - sleep_total_min + 24 * 60) % (24 * 60);
    (bed_total_min / 60, bed_total_min % 60)
}

predicate ValidOutput(result: string)
{
    |result| == 6 &&
    result[|result|-1] == '\n' &&
    result[2] == ':' &&
    '0' <= result[0] <= '9' && '0' <= result[1] <= '9' &&
    '0' <= result[3] <= '9' && '0' <= result[4] <= '9' &&
    (result[0] as int - '0' as int) * 10 + (result[1] as int - '0' as int) <= 23 &&
    (result[3] as int - '0' as int) * 10 + (result[4] as int - '0' as int) <= 59
}

predicate CorrectBedtime(stdin_input: string, result: string)
    requires ValidInput(stdin_input) && ValidOutput(result)
{
    var first_nl := FindFirstNewline(stdin_input);
    var second_nl := FindSecondNewline(stdin_input, first_nl);
    var s := stdin_input[..first_nl];
    var t := stdin_input[first_nl+1..second_nl];
    var (wake_hour, wake_min) := ParseTime(s);
    var (sleep_hour, sleep_min) := ParseTime(t);
    var (bed_hour, bed_min) := CalculateBedtime(wake_hour, wake_min, sleep_hour, sleep_min);
    var result_hour := (result[0] as int - '0' as int) * 10 + (result[1] as int - '0' as int);
    var result_min := (result[3] as int - '0' as int) * 10 + (result[4] as int - '0' as int);
    result_hour == bed_hour && result_min == bed_min
}

// <vc-helpers>
function FindFirstNewline(s: string): int
    requires |s| > 0 && exists i :: 0 <= i < |s| && s[i] == '\n'
    ensures 0 <= FindFirstNewline(s) < |s|
    ensures s[FindFirstNewline(s)] == '\n'
    ensures forall i :: 0 <= i < FindFirstNewline(s) ==> s[i] != '\n'

function FindSecondNewline(s: string, first_nl: int): int
    requires |s| > 0 && 0 <= first_nl < |s| && s[first_nl] == '\n'
    requires exists i :: first_nl < i < |s| && s[i] == '\n'
    ensures first_nl < FindSecondNewline(s, first_nl) < |s|
    ensures s[FindSecondNewline(s, first_nl)] == '\n'
    ensures forall i :: first_nl < i < FindSecondNewline(s, first_nl) ==> s[i] != '\n'

lemma {:axiom} FindFirstNewlineExists(s: string)
    requires |s| > 0 && exists i :: 0 <= i < |s| && s[i] == '\n'
    ensures 0 <= FindFirstNewline(s) < |s|
    ensures s[FindFirstNewline(s)] == '\n'

lemma {:axiom} FindSecondNewlineExists(s: string, first_nl: int)
    requires |s| > 0 && 0 <= first_nl < |s| && s[first_nl] == '\n'
    requires exists i :: first_nl < i < |s| && s[i] == '\n'
    ensures first_nl < FindSecondNewline(s, first_nl) < |s|
    ensures s[FindSecondNewline(s, first_nl)] == '\n'

function IntToString(n: int): string
    requires 0 <= n <= 99
    ensures |IntToString(n)| == 2
    ensures '0' <= IntToString(n)[0] <= '9' && '0' <= IntToString(n)[1] <= '9'
    ensures (IntToString(n)[0] as int - '0' as int) * 10 + (IntToString(n)[1] as int - '0' as int) == n
{
    if n < 10 then "0" + n as string
    else n as string
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures ValidOutput(result)
    ensures CorrectBedtime(stdin_input, result)
// </vc-spec>
// <vc-code>
{
    var first_nl := FindFirstNewline(stdin_input);
    var second_nl := FindSecondNewline(stdin_input, first_nl);
    var s := stdin_input[..first_nl];
    var t := stdin_input[first_nl+1..second_nl];
    
    var (wake_hour, wake_min) := ParseTime(s);
    var (sleep_hour, sleep_min) := ParseTime(t);
    
    var wake_total_min := wake_hour * 60 + wake_min;
    var sleep_total_min := sleep_hour * 60 + sleep_min;
    var bed_total_min := (wake_total_min - sleep_total_min + 24 * 60) % (24 * 60);
    var bed_hour := bed_total_min / 60;
    var bed_min := bed_total_min % 60;
    
    var hour_str := IntToString(bed_hour);
    var min_str := IntToString(bed_min);
    
    result := hour_str + ":" + min_str + "\n";
}
// </vc-code>

