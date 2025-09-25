// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
  requires ValidInput(s)
  ensures CorrectOutput(s, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
