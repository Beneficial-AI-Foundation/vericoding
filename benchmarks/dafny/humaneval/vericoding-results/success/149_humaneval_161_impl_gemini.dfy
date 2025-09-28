// <vc-preamble>

function hasLetter(s: string): bool
{
    exists i :: 0 <= i < |s| && (('A' <= s[i] <= 'Z') || ('a' <= s[i] <= 'z'))
}

function reverseString(s: string): string
    ensures |reverseString(s)| == |s|
{
    if |s| == 0 then s else s[|s|-1..] + reverseString(s[..|s|-1])
}

function swapCase(c: char): char
{
    if 'A' <= c <= 'Z' then (c as int + 32) as char
    else if 'a' <= c <= 'z' then (c as int - 32) as char
    else c
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed char to string conversion for concatenation */
function swapCaseString(s: string): string
    ensures |s| == |swapCaseString(s)|
    ensures forall i :: 0 <= i < |s| ==> swapCaseString(s)[i] == swapCase(s[i])
{
    if |s| == 0 then s
    else [swapCase(s[0])] + swapCaseString(s[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    ensures if hasLetter(s) then
        |result| == |s| && 
        (forall i :: 0 <= i < |s| ==> result[i] == swapCase(s[i]))
    else
        result == reverseString(s)
    ensures |result| == |s|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): used if/else to handle the two cases from the specification */
  if hasLetter(s) {
    result := swapCaseString(s);
  } else {
    result := reverseString(s);
  }
}
// </vc-code>
