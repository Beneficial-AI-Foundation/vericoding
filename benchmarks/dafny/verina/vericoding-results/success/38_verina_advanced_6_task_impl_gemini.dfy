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
predicate VowelFlags(s_prefix: seq<char>, has_a: bool, has_e: bool, has_i: bool, has_o: bool, has_u: bool)
{
    (has_a <==> 'a' in s_prefix) &&
    (has_e <==> 'e' in s_prefix) &&
    (has_i <==> 'i' in s_prefix) &&
    (has_o <==> 'o' in s_prefix) &&
    (has_u <==> 'u' in s_prefix)
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
    var has_a := false;
    var has_e := false;
    var has_i := false;
    var has_o := false;
    var has_u := false;

    var norm_s := NormalizeStr(s);

    var i := 0;
    while i < |norm_s|
        invariant 0 <= i <= |norm_s|
        invariant VowelFlags(norm_s[..i], has_a, has_e, has_i, has_o, has_u)
    {
        var c := norm_s[i];
        if c == 'a' {
            has_a := true;
        } else if c == 'e' {
            has_e := true;
        } else if c == 'i' {
            has_i := true;
        } else if c == 'o' {
            has_o := true;
        } else if c == 'u' {
            has_u := true;
        }
        i := i + 1;
    }
    
    result := has_a && has_e && has_i && has_o && has_u;
}
// </vc-code>
