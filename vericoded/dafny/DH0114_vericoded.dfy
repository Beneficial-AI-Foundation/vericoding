// <vc-preamble>

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
lemma filter_chars_append_lemma(s: seq<char>, ch: char, c: seq<char>)
    ensures filter_chars(s + [ch], c) == 
        (if ch in c then filter_chars(s, c) else filter_chars(s, c) + [ch])
{
    if |s| == 0 {
        assert s + [ch] == [ch];
        if ch in c {
            assert filter_chars([ch], c) == filter_chars(s, c);
        } else {
            assert filter_chars([ch], c) == [ch];
            assert filter_chars(s, c) + [ch] == [] + [ch] == [ch];
        }
    } else {
        assert s + [ch] == [s[0]] + (s[1..] + [ch]);
        filter_chars_append_lemma(s[1..], ch, c);
    }
}
// </vc-preamble>

// <vc-helpers>
lemma reverse_filter_property(s: seq<char>, c: seq<char>)
    ensures |filter_chars(s, c)| <= |s|
    ensures forall i :: 0 <= i < |filter_chars(s, c)| ==> filter_chars(s, c)[i] !in c
    ensures forall i :: 0 <= i < |filter_chars(s, c)| ==> filter_chars(s, c)[i] in s
{
    if |s| == 0 {
    } else if s[0] in c {
        reverse_filter_property(s[1..], c);
    } else {
        reverse_filter_property(s[1..], c);
        assert filter_chars(s, c) == [s[0]] + filter_chars(s[1..], c);
    }
}

function is_palindrome(s: seq<char>): bool
{
    s == reverse(s)
}
// </vc-helpers>

// <vc-spec>
method reverse_delete(s: seq<char>, c: seq<char>) returns (result: (seq<char>, bool))
    ensures result.0 == filter_chars(s, c)
    ensures result.1 == (result.0 == reverse(result.0))
    ensures |result.0| <= |s|
    ensures forall i :: 0 <= i < |result.0| ==> result.0[i] !in c
    ensures forall i :: 0 <= i < |result.0| ==> result.0[i] in s
// </vc-spec>
// <vc-code>
{
    var filtered := filter_chars(s, c);
    var reversed := reverse(filtered);
    var isPalindrome := filtered == reversed;
    
    reverse_filter_property(s, c);
    
    result := (filtered, isPalindrome);
}
// </vc-code>
