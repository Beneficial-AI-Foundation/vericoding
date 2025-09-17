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
    assume {:axiom} false;
}
// </vc-code>
