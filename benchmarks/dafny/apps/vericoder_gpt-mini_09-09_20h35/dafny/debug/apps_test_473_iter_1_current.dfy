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
    ensures 0 <= FindFirstNewline(s) < |s|
    ensures s[FindFirstNewline(s)] == '\n'
    ensures forall k :: 0 <= k < FindFirstNewline(s) ==> s[k] != '\n'
{
    if s[0] == '\n' then 0 else 1 + FindFirstNewline(s[1..])
}

function FindSecondNewline(s: string, first: int): int
    requires 0 <= first < |s|
    requires s[first] == '\n'
    requires first + 1 < |s|
    ensures first < FindSecondNewline(s, first) < |s|
    ensures s[FindSecondNewline(s, first)] == '\n'
    ensures forall k :: first < k < FindSecondNewline(s, first) ==> s[k] != '\n'
{
    first + 1 + FindFirstNewline(s[first+1..])
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

  var c0 := (('0' as int + bed_hour / 10) as char);
  var c1 := (('0' as int + bed_hour % 10) as char);
  var c3 := (('0' as int + bed_min / 10) as char);
  var c4 := (('0' as int + bed_min % 10) as char);

  result := "" + c0 + c1 + ':' + c3 + c4 + '\n';

  // Basic checks to help the verifier
  assert 0 <= bed_hour <= 23;
  assert 0 <= bed_min <= 59;
  assert '0' <= c0 && c0 <= '9';
  assert '0' <= c1 && c1 <= '9';
  assert '0' <= c3 && c3 <= '9';
  assert '0' <= c4 && c4 <= '9';
  assert result[0] == c0;
  assert result[1] == c1;
  assert result[2] == ':';
  assert result[3] == c3;
  assert result[4] == c4;
  assert result[5] == '\n';
  assert |result| == 6;

  assert ValidOutput(result);
  assert CorrectBedtime(stdin_input, result);
}
// </vc-code>

