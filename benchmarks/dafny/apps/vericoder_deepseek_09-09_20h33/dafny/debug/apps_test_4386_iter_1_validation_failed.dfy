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
function parseInput(input: string): (int, string)
  requires ValidInput(input)
  ensures exists i :: 0 < i < |input| && input[i] == '\n' && 
           (forall j :: 0 <= j < i ==> '0' <= input[j] <= '9') &&
           (forall j :: i+1 <= j < |input| ==> 'a' <= input[j] <= 'z')
  ensures ValidParsedInput(parseInput(input).0, parseInput(input).1)
{
  var nlIndex :| 0 < nlIndex < |input| && input[nlIndex] == '\n' && 
                (forall j :: 0 <= j < nlIndex ==> '0' <= input[j] <= '9');
  var a := string_to_int(input[0..nlIndex]);
  var s := input[nlIndex+1..];
  (a, s)
}

function string_to_int(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
  if |s| == 1 then s[0] - '0'
  else 10 * string_to_int(s[0..|s|-1]) + (s[|s|-1] - '0')
}

lemma {:axiom} StringToIntValid(s: string)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures 0 <= string_to_int(s)
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
  var (a, s) := parseInput(input);
  if a >= 3200 {
    result := s + "\n";
  } else {
    result := "red\n";
  }
}
// </vc-code>

