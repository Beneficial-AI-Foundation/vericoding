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
function IsVowel(c: char): bool
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

function InNormalize(s: string, c: char): bool
{
    c in NormalizeStr(s)
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
  var n := NormalizeStr(s);
  result := ('a' in n) && ('e' in n) && ('i' in n) && ('o' in n) && ('u' in n);
}
// </vc-code>
