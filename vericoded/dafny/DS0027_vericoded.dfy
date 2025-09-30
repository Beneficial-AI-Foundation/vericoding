// <vc-preamble>
predicate IsAlphaChar(c: char)
{
    ('A' <= c <= 'Z') || ('a' <= c <= 'z')
}

predicate StringIsAlpha(s: seq<char>)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> IsAlphaChar(s[i])
}
// </vc-preamble>

// <vc-helpers>
function SeqIsAlpha(s: seq<char>): bool
{
  |s| > 0 && forall k :: 0 <= k < |s| ==> IsAlphaChar(s[k])
}
// </vc-helpers>

// <vc-spec>
method IsAlpha(input: array<string>) returns (ret: array<bool>)
    ensures
        ret.Length == input.Length &&
        forall i :: 0 <= i < input.Length ==> 
            ret[i] == StringIsAlpha(input[i])
// </vc-spec>
// <vc-code>
{
  ret := new bool[input.Length];
  var i := 0;
  while i < input.Length
    invariant 0 <= i <= input.Length
    invariant ret.Length == input.Length
    invariant forall j :: 0 <= j < i ==> ret[j] == StringIsAlpha(input[j])
  {
    ret[i] := StringIsAlpha(input[i]);
    i := i + 1;
  }
}
// </vc-code>
