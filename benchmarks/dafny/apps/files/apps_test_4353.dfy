Given a string containing comma-separated words, replace all commas with spaces.
The input string has length 19 with format: 5 lowercase letters, comma, 7 lowercase letters, comma, 5 lowercase letters.

predicate ValidInput(s: string)
{
  |s| == 19 && 
  |s| >= 2 && s[5] == ',' && s[13] == ',' &&
  forall i :: 0 <= i < |s| ==> (s[i] == ',' || ('a' <= s[i] <= 'z'))
}

function CommasToSpaces(s: string): string
  requires ValidInput(s)
{
  seq(|s|, i requires 0 <= i < |s| => if s[i] == ',' then ' ' else s[i])
}

predicate CorrectOutput(s: string, result: string)
  requires ValidInput(s)
{
  |result| == |s| + 1 &&
  result[|result| - 1] == '\n' &&
  forall i :: 0 <= i < |s| ==> 
    (s[i] == ',' ==> result[i] == ' ') &&
    (s[i] != ',' ==> result[i] == s[i])
}

method solve(s: string) returns (result: string)
  requires ValidInput(s)
  ensures CorrectOutput(s, result)
{
  var chars: seq<char> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |chars| == i
    invariant forall j :: 0 <= j < i ==> 
      (s[j] == ',' ==> chars[j] == ' ') &&
      (s[j] != ',' ==> chars[j] == s[j])
  {
    if s[i] == ',' {
      chars := chars + [' '];
    } else {
      chars := chars + [s[i]];
    }
    i := i + 1;
  }
  result := chars + ['\n'];
}
