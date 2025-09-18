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
function containsChar(s: seq<char>, c: char): bool
{
    exists i :: 0 <= i < |s| && s[i] == c
}
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
    var normalized_s := NormalizeStr(s);
    result := containsChar(normalized_s, 'a') &&
              containsChar(normalized_s, 'e') &&
              containsChar(normalized_s, 'i') &&
              containsChar(normalized_s, 'o') &&
              containsChar(normalized_s, 'u');
}
// </vc-code>
