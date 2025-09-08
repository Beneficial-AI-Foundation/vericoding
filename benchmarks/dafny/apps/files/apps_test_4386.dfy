Given an integer a and a string s of lowercase English letters, 
output s if a >= 3200, otherwise output "red".

predicate ValidInput(input: string)
{
  |input| > 0 &&
  (exists i :: 0 < i < |input| && input[i] == '\n') &&
  (forall i :: 0 <= i < |input| ==> input[i] == '\n' || ('0' <= input[i] <= '9') || ('a' <= input[i] <= 'z')) &&
  (exists i :: 0 < i < |input| && input[i] == '\n' && (forall j :: 0 <= j < i ==> '0' <= input[j] <= '9'))
}

predicate ValidParsedInput(a: int, s: string)
{
  2800 <= a < 5000 &&
  1 <= |s| <= 10 &&
  (forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z')
}

predicate CorrectOutput(a: int, s: string, result: string)
{
  (a >= 3200 ==> result == s + "\n") &&
  (a < 3200 ==> result == "red\n")
}

function StringToInt(s: string): int
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  requires |s| > 0
{
  if |s| == 1 then
    (s[0] as int) - ('0' as int)
  else
    StringToInt(s[0..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

function FindDigitNewline(s: string, start: int): int
  requires 0 <= start <= |s|
  requires exists i :: start <= i < |s| && s[i] == '\n' && (forall j :: 0 <= j < i ==> '0' <= s[j] <= '9')
  ensures start <= FindDigitNewline(s, start) < |s|
  ensures s[FindDigitNewline(s, start)] == '\n'
  ensures forall j :: 0 <= j < FindDigitNewline(s, start) ==> '0' <= s[j] <= '9'
  decreases |s| - start
{
  if start >= |s| then start
  else if s[start] == '\n' && (forall j :: 0 <= j < start ==> '0' <= s[j] <= '9') then start
  else FindDigitNewline(s, start + 1)
}

function FindNewline(s: string, start: int): int
  requires 0 <= start <= |s|
  ensures -1 <= FindNewline(s, start) < |s|
  ensures FindNewline(s, start) >= -1
  ensures FindNewline(s, start) == -1 ==> forall i :: start <= i < |s| ==> s[i] != '\n'
  ensures FindNewline(s, start) >= 0 ==> start <= FindNewline(s, start) < |s| && s[FindNewline(s, start)] == '\n'
  decreases |s| - start
{
  if start >= |s| then -1
  else if s[start] == '\n' then start
  else FindNewline(s, start + 1)
}

function parseInput(input: string): (int, string)
  requires ValidInput(input)
  ensures exists newlineIndex :: 0 < newlineIndex < |input| && input[newlineIndex] == '\n'
{
  var newlineIndex := FindDigitNewline(input, 1);
  assert newlineIndex >= 1 && newlineIndex < |input| && input[newlineIndex] == '\n';
  assert forall j :: 0 <= j < newlineIndex ==> '0' <= input[j] <= '9';
  var aStr := input[0..newlineIndex];
  var remaining := input[newlineIndex+1..];
  var secondNewline := if |remaining| > 0 then FindNewline(remaining, 0) else |remaining|;
  var s := if secondNewline >= 0 then remaining[0..secondNewline] else remaining;
  (StringToInt(aStr), s)
}

method solve(input: string) returns (result: string)
  requires ValidInput(input)
  requires exists a: int, s: string :: 
    parseInput(input) == (a, s) && ValidParsedInput(a, s)
  ensures exists a: int, s: string :: 
    parseInput(input) == (a, s) && 
    ValidParsedInput(a, s) &&
    CorrectOutput(a, s, result)
  ensures |result| > 0
  ensures result[|result|-1] == '\n'
  ensures (exists a: int, s: string :: 
    parseInput(input) == (a, s) && a >= 3200) ==> 
    (exists s: string :: result == s + "\n" && 1 <= |s| <= 10 && (forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z'))
  ensures (exists a: int, s: string :: 
    parseInput(input) == (a, s) && a < 3200) ==> result == "red\n"
{
    var (a, s) := parseInput(input);

    if a >= 3200 {
        result := s + "\n";
    } else {
        result := "red\n";
    }
}
