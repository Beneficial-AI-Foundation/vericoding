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
  reads s
  requires exists i :: 0 <= i < |s| && s[i] == '\n'
  ensures 0 <= FindFirstNewline(s) < |s|
  ensures s[FindFirstNewline(s)] == '\n'
  ensures forall k :: 0 <= k < FindFirstNewline(s) ==> s[k] != '\n'
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> s[k] != '\n'
  {
    if s[i] == '\n' then
      return i;
    i := i + 1;
  }
  // This point should not be reachable due to the `requires` clause
  -1 // Should not happen
}

function FindSecondNewline(s: string, first_nl_pos: int): int
  reads s
  requires 0 <= first_nl_pos < |s|
  requires s[first_nl_pos] == '\n'
  requires exists i :: first_nl_pos < i < |s| && s[i] == '\n'
  ensures first_nl_pos < FindSecondNewline(s, first_nl_pos) < |s|
  ensures s[FindSecondNewline(s, first_nl_pos)] == '\n'
  ensures forall k :: first_nl_pos < k < FindSecondNewline(s, first_nl_pos) ==> s[k] != '\n'
{
  var i := first_nl_pos + 1;
  while i < |s|
    invariant first_nl_pos < i <= |s|
    invariant forall k :: first_nl_pos < k < i ==> s[k] != '\n'
  {
    if s[i] == '\n' then
      return i;
    i := i + 1;
  }
  // This point should not be reachable due to the `requires` clause
  -1 // Should not happen
}

function DigitToChar(d: int): char
  requires 0 <= d <= 9
  ensures '0' <= DigitToChar(d) <= '9'
{
  ('0' as int + d) as char
}

function IntToTwoDigitString(n: int): (string)
  requires 0 <= n <= 99
  ensures |IntToTwoDigitString(n)| == 2
  ensures (IntToTwoDigitString(n))[0] == (n / 10 + '0' as int) as char
  ensures (IntToTwoDigitString(n))[1] == (n % 10 + '0' as int) as char
{
  var tens := n / 10;
  var ones := n % 10;
  var h_char := DigitToChar(tens);
  var t_char := DigitToChar(ones);
  h_char as string + t_char as string
}

lemma IntToTwoDigitString_properties(n: int)
  requires 0 <= n <= 99
  ensures var s := IntToTwoDigitString(n);
          (s[0] as int - '0' as int) * 10 + (s[1] as int - '0' as int) == n
{
  var s := IntToTwoDigitString(n);
  // Proof that (h_char as int - '0' as int) * 10 == n / 10 * 10
  // n / 10 * 10 + n % 10 == n (division property)
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
    
    var bed_hour_str := IntToTwoDigitString(bed_hour);
    var bed_min_str := IntToTwoDigitString(bed_min);

    // Provide proof that the calculated bed_hour and bed_min are within 0..23 and 0..59 respectively
    // This is handled by CalculateBedtime's ensures clause.

    // Using properties of IntToTwoDigitString to ensure the string content is correct for CorrectBedtime
    ghost var _ := IntToTwoDigitString_properties(bed_hour);
    ghost var _ := IntToTwoDigitString_properties(bed_min);

    result := bed_hour_str + ":" + bed_min_str + "\n";
}
// </vc-code>

