predicate ValidInput(s: string)
{
    |s| >= 1 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

function ExpectedLength(s: string): nat
{
    (|s| + 1) / 2
}

predicate CorrectExtraction(s: string, result: string)
{
    |result| == ExpectedLength(s) &&
    forall i :: 0 <= i < |result| ==> 0 <= 2*i < |s| && result[i] == s[2*i] &&
    forall i :: 0 <= i < |s| && i % 2 == 0 ==> exists j :: 0 <= j < |result| && result[j] == s[i] && j == i / 2
}

// <vc-helpers>
function Chars2String(chars: seq<char>): string
  ensures |Chars2String(chars)| == |chars|
  ensures forall i :: 0 <= i < |chars| ==> Chars2String(chars)[i] == chars[i]
{
  if |chars| == 0 then "" else Chars2String(chars[..|chars|-1]) + (chars[|chars|-1] as string)
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures CorrectExtraction(s, result)
// </vc-spec>
// <vc-code>
{
    var len := ExpectedLength(s);
    var chars := new char[len];
    var i := 0;
    while i < len
        invariant 0 <= i <= len
        invariant forall j :: 0 <= j < i ==> chars[j] == s[2*j]
        invariant forall j :: i <= j < len ==> chars[j] == '\0' 
        decreases len - i
    {
        chars[i] := s[2*i];
        i := i + 1;
    }
    result := Chars2String(chars[..]);
}
// </vc-code>

