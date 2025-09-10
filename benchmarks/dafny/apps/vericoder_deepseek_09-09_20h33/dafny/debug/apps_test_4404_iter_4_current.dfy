predicate IsValidDateString(s: string, y: int, m: int, d: int)
{
    |s| >= 10 && 
    s[4] == '/' && s[7] == '/' &&
    StringToInt(s[0..4]) == y &&
    StringToInt(s[5..7]) == m &&
    StringToInt(s[8..10]) == d
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then CharToDigit(s[0])
    else if |s| == 2 then CharToDigit(s[0]) * 10 + CharToDigit(s[1])
    else if |s| == 4 then CharToDigit(s[0]) * 1000 + CharToDigit(s[1]) * 100 + CharToDigit(s[2]) * 10 + CharToDigit(s[3])
    else 0
}

function CharToDigit(c: char): int
{
    if '0' <= c <= '9' then (c as int) - ('0' as int) else 0
}

predicate ValidInput(s: string)
{
    exists y, m, d :: IsValidDateString(s, y, m, d) && y == 2019 && 1 <= m <= 12 && 1 <= d <= 31
}

predicate CorrectOutput(s: string, result: string)
{
    exists y, m, d :: IsValidDateString(s, y, m, d) && y == 2019 && 1 <= m <= 12 && 1 <= d <= 31 && 
    ((m < 4 || (m == 4 && d <= 30)) ==> result == "Heisei") && 
    ((m > 4 || (m == 4 && d > 30)) ==> result == "TBD")
}

// <vc-helpers>
lemma StringToIntCorrect(s: string, expected: int)
  requires |s| == 4 && forall i :: 0 <= i < 4 ==> '0' <= s[i] <= '9'
  ensures StringToInt(s) == expected
{
}

lemma ExtractDateParts(s: string, y: int, m: int, d: int)
  requires IsValidDateString(s, y, m, d) && y == 2019
  ensures StringToInt(s[0..4]) == 2019 &&
          1 <= StringToInt(s[5..7]) <= 12 &&
          1 <= StringToInt(s[8..10]) <= 31
{
  assert StringToInt(s[0..4]) == y;
  assert StringToInt(s[5..7]) == m;
  assert StringToInt(s[8..10]) == d;
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
requires |stdin_input| > 0
requires ValidInput(stdin_input)
ensures CorrectOutput(stdin_input, result)
// </vc-spec>
// <vc-code>
{
  var y : int, m : int, d : int :| IsValidDateString(stdin_input, y, m, d) && y == 2019 && 1 <= m <= 12 && 1 <= d <= 31;
  ExtractDateParts(stdin_input, y, m, d);
  var year := StringToInt(stdin_input[0..4]);
  var month := StringToInt(stdin_input[5..7]);
  var day := StringToInt(stdin_input[8..10]);
  
  assert year == 2019;
  assert 1 <= month <= 12;
  assert 1 <= day <= 31;
  
  if month < 4 || (month == 4 && day <= 30) {
    result := "Heisei";
  } else {
    result := "TBD";
  }
}
// </vc-code>

