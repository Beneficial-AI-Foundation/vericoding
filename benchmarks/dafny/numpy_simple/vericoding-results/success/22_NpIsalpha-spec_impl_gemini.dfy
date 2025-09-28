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
method CheckStringIsAlpha(s: seq<char>) returns (is_alpha: bool)
    ensures is_alpha == StringIsAlpha(s)
{
    if |s| == 0 {
        is_alpha := false;
        return;
    }
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> IsAlphaChar(s[j])
    {
        if !IsAlphaChar(s[i]) {
            is_alpha := false;
            return;
        }
        i := i + 1;
    }
    is_alpha := true;
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
        var is_alpha_string := CheckStringIsAlpha(input[i]);
        ret[i] := is_alpha_string;
        i := i + 1;
    }
}
// </vc-code>
