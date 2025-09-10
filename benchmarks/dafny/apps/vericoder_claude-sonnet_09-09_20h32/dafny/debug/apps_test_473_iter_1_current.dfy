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
    requires |s| > 0
    requires exists i :: 0 <= i < |s| && s[i] == '\n'
    ensures 0 <= FindFirstNewline(s) < |s|
    ensures s[FindFirstNewline(s)] == '\n'
    ensures forall j :: 0 <= j < FindFirstNewline(s) ==> s[j] != '\n'
{
    if s[0] == '\n' then 0
    else 1 + FindFirstNewline(s[1..])
}

function FindSecondNewline(s: string, first: int): int
    requires 0 <= first < |s|
    requires s[first] == '\n'
    requires exists i :: first < i < |s| && s[i] == '\n'
    ensures first < FindSecondNewline(s, first) < |s|
    ensures s[FindSecondNewline(s, first)] == '\n'
    ensures forall j :: first < j < FindSecondNewline(s, first) ==> s[j] != '\n'
{
    FindFirstNewlineAfter(s, first + 1)
}

function FindFirstNewlineAfter(s: string, start: int): int
    requires 0 <= start < |s|
    requires exists i :: start <= i < |s| && s[i] == '\n'
    ensures start <= FindFirstNewlineAfter(s, start) < |s|
    ensures s[FindFirstNewlineAfter(s, start)] == '\n'
    ensures forall j :: start <= j < FindFirstNewlineAfter(s, start) ==> s[j] != '\n'
{
    if s[start] == '\n' then start
    else 1 + FindFirstNewlineAfter(s, start + 1)
}

function IntToChar(n: int): char
    requires 0 <= n <= 9
    ensures IntToChar(n) as int == '0' as int + n
{
    ('0' as int + n) as char
}

function FormatTime(hour: int, min: int): string
    requires 0 <= hour <= 23 && 0 <= min <= 59
    ensures |FormatTime(hour, min)| == 6
    ensures FormatTime(hour, min)[5] == '\n'
    ensures FormatTime(hour, min)[2] == ':'
    ensures ValidOutput(FormatTime(hour, min))
{
    var h1 := IntToChar(hour / 10);
    var h2 := IntToChar(hour % 10);
    var m1 := IntToChar(min / 10);
    var m2 := IntToChar(min % 10);
    [h1, h2, ':', m1, m2, '\n']
}

lemma FormatTimeCorrect(hour: int, min: int)
    requires 0 <= hour <= 23 && 0 <= min <= 59
    ensures var result := FormatTime(hour, min);
            var result_hour := (result[0] as int - '0' as int) * 10 + (result[1] as int - '0' as int);
            var result_min := (result[3] as int - '0' as int) * 10 + (result[4] as int - '0' as int);
            result_hour == hour && result_min == min
{
    var result := FormatTime(hour, min);
    var h1 := IntToChar(hour / 10);
    var h2 := IntToChar(hour % 10);
    var m1 := IntToChar(min / 10);
    var m2 := IntToChar(min % 10);
    
    assert result[0] == h1;
    assert result[1] == h2;
    assert result[3] == m1;
    assert result[4] == m2;
    
    assert h1 as int == '0' as int + hour / 10;
    assert h2 as int == '0' as int + hour % 10;
    assert m1 as int == '0' as int + min / 10;
    assert m2 as int == '0' as int + min % 10;
    
    var result_hour := (result[0] as int - '0' as int) * 10 + (result[1] as int - '0' as int);
    var result_min := (result[3] as int - '0' as int) * 10 + (result[4] as int - '0' as int);
    
    assert result_hour == (hour / 10) * 10 + (hour % 10);
    assert result_min == (min / 10) * 10 + (min % 10);
    assert result_hour == hour;
    assert result_min == min;
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
    var (bed_hour, bed_min) := CalculateBedtime(wake_hour, wake_min, sleep_hour, sleep_min);
    
    result := FormatTime(bed_hour, bed_min);
    
    FormatTimeCorrect(bed_hour, bed_min);
}
// </vc-code>

