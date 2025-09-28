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
lemma NonLetterSwapCase(s: string)
  ensures forall i :: 0 <= i < |s| && !(('A' <= s[i] <= 'Z') || ('a' <= s[i] <= 'z')) ==> swapCase(s[i]) == s[i]
{
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
  if hasLetter(s) {
    var r := s;
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant |r| == |s|
      invariant forall j :: 0 <= j < i ==> r[j] == swapCase(s[j])
      invariant forall j :: i <= j < |s| ==> r[j] == s[j]
      decreases |s| - i
    {
      r := r[i := swapCase(s[i])];
      i := i + 1;
    }
    result := r;
  } else {
    result := reverseString(s);
  }
}
// </vc-code>
