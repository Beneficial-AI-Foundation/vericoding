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
function parseInput(input: string) : (int, string)
  requires ValidInput(input)
  ensures var a := parseInput(input).0; var s := parseInput(input).1;
          exists i :: 0 < i < |input| && input[i] == '\n' &&
                      (forall j :: 0 <= j < i ==> '0' <= input[j] <= '9') &&
                      a == StringToInt(input[0..i]) &&
                      s == input[i+1 ..]
{
  var i := 0;
  while i < |input| && input[i] != '\n'
    invariant 0 <= i <= |input|
    invariant (forall j :: 0 <= j < i ==> '0' <= input[j] <= '9')
  {
    i := i + 1;
  }
  var a := StringToInt(input[0..i]);
  var s := input[i+1 ..];
  return (a, s);
}

function StringToInt(s: string) : int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
  if |s| == 1 then
    (s[0] as int) - ('0' as int)
  else
    StringToInt(s[0 .. |s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
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
  var a, s := parseInput(input);
  if a >= 3200 {
    result := s + "\n";
  } else {
    result := "red\n";
  }
  return result;
}
// </vc-code>

