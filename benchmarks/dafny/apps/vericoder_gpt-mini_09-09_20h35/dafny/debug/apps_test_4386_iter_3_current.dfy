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

// <vc-helpers>
function pow10(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else 10 * pow10(n - 1)
}

function charToDigit(c: char): int
  requires '0' <= c <= '9'
{
  if c == '0' then 0
  else if c == '1' then 1
  else if c == '2' then 2
  else if c == '3' then 3
  else if c == '4' then 4
  else if c == '5' then 5
  else if c == '6' then 6
  else if c == '7' then 7
  else if c == '8' then 8
  else 9
}

function parseNum(input: string, i: int): (int, int, int)
  requires 0 <= i < |input|
  // there is a newline at or after i, and all characters from i up to (but not including) that newline are digits
  requires exists j :: i <= j < |input__?__| && input[j] == '\n' && (forall k :: i <= k < j ==> '0' <= input[k] <= '9')
  decreases |input| - i
  ensures 0 <= result.1
  ensures i <= result.2 < |input|
  ensures forall k :: i <= k < result.2 ==> '0' <= input[k] <= '9'
{
  if input[i] == '\n' then (0, 0, i)
  else
    // From the precondition there exists a newline j >= i with digits up to j.
    // Since input[i] != '\n', that newline must be at index > i, so the precondition also holds for i+1.
    assert exists j :: i <= j < |input__?__| && input[j] == '\n' && (forall k :: i <= k < j ==> '0' <= input[k] <= '9');
    // Using the precondition and input[i] != '\n' we can conclude input[i] is a digit.
    assert '0' <= input[i] <= '9';
    var t := parseNum(input, i + 1);
    var v := t.0;
    var len := t.1;
    var j := t.2;
    // len is non-negative by the ensures of the recursive call
    assert 0 <= len;
    (charToDigit(input[i]) * pow10(len) + v, len + 1, j)
}

function parseInput(input: string): (int, string)
  requires |input| > 0
  requires exists i :: 0 < i < |input| && input[i] == '\n' && (forall j :: 0 <= j < i ==> '0' <= input[j] <= '9')
{
  var t := parseNum(input, 0);
  (t.0, input[t.2 + 1 .. |input|])
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
  var a, s :| parseInput(input) == (a, s) && ValidParsedInput(a, s);
  if a >= 3200 {
    result := s + "\n";
  } else {
    result := "red\n";
  }
}
// </vc-code>

