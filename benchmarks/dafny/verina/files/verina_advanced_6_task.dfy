// <vc-preamble>
function ToLower(c: char): char
{
    if 'A' <= c <= 'Z' then
        (c as int + 32) as char
    else
        c
}

function NormalizeStr(s: string): seq<char>
{
    seq(|s|, i requires 0 <= i < |s| => ToLower(s[i]))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method AllVowels(s: string) returns (result: bool)
    ensures
        result <==> (
            'a' in NormalizeStr(s) &&
            'e' in NormalizeStr(s) &&
            'i' in NormalizeStr(s) &&
            'o' in NormalizeStr(s) &&
            'u' in NormalizeStr(s)
        )
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    // impl-end
}
// </vc-code>
