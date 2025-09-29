// <vc-preamble>
predicate IsAlphanumeric(c: char)
{
    ('a' <= c <= 'z') || ('A' <= c <= 'Z') || ('0' <= c <= '9')
}

function ToLowercase(c: char): char
{
    if 'A' <= c <= 'Z' then
        ((c as int) + 32) as char
    else
        c
}

function FilterAlphanumeric(s: seq<char>): seq<char>
{
    if |s| == 0 then []
    else if IsAlphanumeric(s[0]) then [ToLowercase(s[0])] + FilterAlphanumeric(s[1..])
    else FilterAlphanumeric(s[1..])
}
// </vc-preamble>

// <vc-helpers>
predicate IsPalindrome(s: seq<char>)
{
    forall i :: 0 <= i < |s| ==> s[i] == s[|s| - 1 - i]
}

lemma PalindromeEquivalence(s: seq<char>)
    ensures IsPalindrome(s) <==> s == seq(|s|, i requires 0 <= i < |s| => s[|s| - 1 - i])
{
    if IsPalindrome(s) {
        assert s == seq(|s|, i requires 0 <= i < |s| => s[|s| - 1 - i]) by {
            assert forall i :: 0 <= i < |s| ==> s[i] == s[|s| - 1 - i];
        }
    }
    if s == seq(|s|, i requires 0 <= i < |s| => s[|s| - 1 - i]) {
        assert IsPalindrome(s) by {
            forall i | 0 <= i < |s|
            ensures s[i] == s[|s| - 1 - i]
            {
                assert s[i] == (seq(|s|, j requires 0 <= j < |s| => s[|s| - 1 - j]))[i];
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method PalindromeIgnoreNonAlnum(s: string) returns (result: bool)
    ensures 
        result <==> (
            var cleaned := FilterAlphanumeric(s[..]);
            var backward := seq(|cleaned|, i requires 0 <= i < |cleaned| => cleaned[|cleaned| - 1 - i]);
            cleaned == backward
        )
// </vc-spec>
// <vc-code>
{
    var cleaned := FilterAlphanumeric(s[..]);
    var i := 0;
    result := true;
    
    while i < |cleaned| / 2
        invariant 0 <= i <= |cleaned| / 2
        invariant result <==> forall j :: 0 <= j < i ==> cleaned[j] == cleaned[|cleaned| - 1 - j]
    {
        if cleaned[i] != cleaned[|cleaned| - 1 - i] {
            result := false;
            break;
        }
        i := i + 1;
    }
    
    if result {
        PalindromeEquivalence(cleaned);
    }
}
// </vc-code>
