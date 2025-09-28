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

function StringToSeq(s: string): seq<char>
{
    s[..]
}

lemma StringIsAlphaLemma(s: string)
    ensures StringIsAlpha(StringToSeq(s)) == (|s| > 0 && forall i :: 0 <= i < |s| ==> IsAlphaChar(s[i]))
{
}

function StringIsAlphaImpl(s: string): bool
    ensures StringIsAlphaImpl(s) == StringIsAlpha(StringToSeq(s))
{
    if |s| == 0 then false
    else (forall i :: 0 <= i < |s| ==> IsAlphaChar(s[i]))
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
    /* code modified by LLM (iteration 2): Added proper loop invariants and helper function usage */
    ret := new bool[input.Length];
    var idx := 0;
    while idx < input.Length
        invariant 0 <= idx <= input.Length
        invariant ret.Length == input.Length
        invariant forall i :: 0 <= i < idx ==> ret[i] == StringIsAlphaImpl(input[i])
    {
        var currentString := input[idx];
        ret[idx] := StringIsAlphaImpl(currentString);
        idx := idx + 1;
    }
}
// </vc-code>
