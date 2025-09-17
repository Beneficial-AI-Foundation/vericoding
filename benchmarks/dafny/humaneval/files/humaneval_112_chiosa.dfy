// <vc-preamble>
// ======= TASK =======
// Given two strings s and c, remove all characters from string s that appear 
// anywhere in string c. Then determine if the resulting string is a palindrome 
// (reads the same forwards and backwards). Return a tuple containing the 
// filtered string and a boolean indicating whether it's a palindrome.

// ======= SPEC REQUIREMENTS =======
function filter_chars(s: seq<char>, c: seq<char>): seq<char>
{
    if |s| == 0 then []
    else if s[0] in c then filter_chars(s[1..], c)
    else [s[0]] + filter_chars(s[1..], c)
}

function reverse(s: seq<char>): seq<char>
{
    if |s| == 0 then []
    else reverse(s[1..]) + [s[0]]
}
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
lemma filter_chars_append_lemma(s: seq<char>, ch: char, c: seq<char>)
    ensures filter_chars(s + [ch], c) == 
        (if ch in c then filter_chars(s, c) else filter_chars(s, c) + [ch])
{
    if |s| == 0 {
        // Base case: s is empty
        assert s + [ch] == [ch];
        if ch in c {
            assert filter_chars([ch], c) == filter_chars(s, c);
        } else {
            assert filter_chars([ch], c) == [ch];
            assert filter_chars(s, c) + [ch] == [] + [ch] == [ch];
        }
    } else {
        // Recursive case
        assert s + [ch] == [s[0]] + (s[1..] + [ch]);
        filter_chars_append_lemma(s[1..], ch, c);
    }
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method reverse_delete(s: seq<char>, c: seq<char>) returns (result: (seq<char>, bool))
    ensures result.0 == filter_chars(s, c)
    ensures result.1 == (result.0 == reverse(result.0))
    ensures |result.0| <= |s|
    ensures forall i :: 0 <= i < |result.0| ==> result.0[i] !in c
    ensures forall i :: 0 <= i < |result.0| ==> result.0[i] in s
// </vc-spec>
// <vc-code>
{
    // Filter out characters that appear in c
    var filtered := [];
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant filtered == filter_chars(s[..i], c)
        invariant |filtered| <= i
        invariant forall j :: 0 <= j < |filtered| ==> filtered[j] !in c
        invariant forall j :: 0 <= j < |filtered| ==> filtered[j] in s[..i]
    {
        if s[i] !in c {
            filtered := filtered + [s[i]];
        }
        assert s[..(i+1)] == s[..i] + [s[i]];
        filter_chars_append_lemma(s[..i], s[i], c);
        assert filtered == filter_chars(s[..(i+1)], c);
    }

    assert s[..|s|] == s;
    assert filtered == filter_chars(s, c);

    // Check if palindrome
    var is_palindrome := filtered == reverse(filtered);

    result := (filtered, is_palindrome);
}
// </vc-code>
