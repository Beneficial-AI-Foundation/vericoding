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

function parseNum(input: string, i: int): (int, int, int)
  requires 0 <= i < |input|
  requires exists j :: i < j < |input| && input[j] == '\n'
  decreases |input| - i
{
  if input[i] == '\n' then (0, 0, i)
  else
    var t := parseNum(input, i + 1);
    var v := t.0;
    var len := t.1;
    var j := t.2;
    var digit := ord(input[i]) - ord('0');
    (digit * pow10(len) + v, len + 1, j)
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

