// <vc-preamble>

function to_lower(c: char): char
{
    if 'A' <= c <= 'Z' then
        (c as int - 'A' as int + 'a' as int) as char
    else
        c
}

predicate IsPalindrome(text: string)
{
    forall i :: 0 <= i < |text| ==> to_lower(text[i]) == to_lower(text[|text| - 1 - i])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Changed `fun` to `function` to fix compilation error */
function is_match(c1: char, c2: char): bool {
    to_lower(c1) == to_lower(c2)
}
// </vc-helpers>

// <vc-spec>
method is_palindrome(text: string) returns (result: bool)
  ensures result <==> IsPalindrome(text)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Provided an implementation that checks for palindrome using the helper method `is_match` */
{
    var n := |text|;
    if n == 0 || n == 1 {
        return true;
    }

    var i := 0;
    while i < n / 2
        invariant 0 <= i <= n / 2
        invariant forall k :: 0 <= k < i ==> is_match(text[k], text[n - 1 - k])
    {
        if !is_match(text[i], text[n - 1 - i]) {
            return false;
        }
        i := i + 1;
    }
    return true;
}
// </vc-code>
