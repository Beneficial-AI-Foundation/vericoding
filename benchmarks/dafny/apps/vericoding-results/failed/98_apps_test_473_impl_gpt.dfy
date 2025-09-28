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
lemma DigitCharFacts(d:int)
  requires 0 <= d <= 9
  ensures 0 <= ('0' as int) + d <= '9' as int
  ensures ((('0' as int) + d) as char) as int - '0' as int == d
  ensures '0' <= ((('0' as int) + d) as char) <= '9'
{
  assert 0 <= ('0' as int) + d <= '9' as int;
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
  var t := stdin_input[first_nl + 1 .. second_nl];

  var wake_hour, wake_min := ParseTime(s);
  var sleep_hour, sleep_min := ParseTime(t);
  var bed_hour, bed_min := CalculateBedtime(wake_hour, wake_min, sleep_hour, sleep_min);

  var h_t := bed_hour / 10;
  var h_o := bed_hour % 10;
  var m_t := bed_min / 10;
  var m_o := bed_min % 10;

  DigitCharFacts(h_t);
  DigitCharFacts(h_o);
  DigitCharFacts(m_t);
  DigitCharFacts(m_o);

  var c0: char := (('0' as int) + h_t) as char;
  var c1: char := (('0' as int) + h_o) as char;
  var c2: char := (('0' as int) + m_t) as char;
  var c3: char := (('0' as int) + m_o) as char;

  result := [c0, c1, ':', c2, c3, '\n'];

  assert (result[0] as int - '0' as int) == h_t;
  assert (result[1] as int - '0' as int) == h_o;
  assert (result[3] as int - '0' as int) == m_t;
  assert (result[4] as int - '0' as int) == m_o;

  assert 10 * (bed_hour / 10) + bed_hour % 10 == bed_hour;
  assert 10 * (bed_min / 10) + bed_min % 10 == bed_min;

  assert (result[0] as int - '0' as int) * 10 + (result[1] as int - '0' as int) == bed_hour;
  assert (result[3] as int - '0' as int) * 10 + (result[4] as int - '0' as int) == bed_min;
}
// </vc-code>

