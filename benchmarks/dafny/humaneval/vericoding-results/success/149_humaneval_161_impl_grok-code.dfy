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
  /* code modified by LLM (iteration 4): Added loop invariants for verification and fixed structure */
  if hasLetter(s) {
    result := [];
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant |result| == i
      invariant forall k :: 0 <= k < i ==> result[k] == swapCase(s[k])
    {
      result := result + [swapCase(s[i])];
      i := i + 1;
    }
  } else {
    result := reverseString(s);
  }
}
// </vc-code>
