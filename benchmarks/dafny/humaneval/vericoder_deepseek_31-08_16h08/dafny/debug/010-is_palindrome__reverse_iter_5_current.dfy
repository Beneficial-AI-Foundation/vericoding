function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}
method make_palindrome(s: string) returns (result: string)
    // post-conditions-start
    ensures |result| <= 2 * |s|
    ensures is_palindrome(result)
    ensures starts_with(result, s)
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma reverse_preserves_palindrome(s: string)
    requires is_palindrome(s)
    ensures reverse(s) == s
{
}

lemma reverse_append_palindrome(s: string)
    ensures is_palindrome(s + reverse(s))
{
}

lemma starts_with_self(s: string)
    ensures starts_with(s, s)
{
}

lemma starts_with_concat(s1: string, s2: string)
    ensures starts_with(s1 + s2, s1)
{
}

function reverse_func(s: string): string
    ensures |reverse_func(s)| == |s|
    ensures forall k :: 0 <= k < |s| ==> reverse_func(s)[k] == s[|s| - 1 - k]
{
    if |s| == 0 then ""
    else [s[|s| - 1]] + reverse_func(s[0..|s| - 1])
}

lemma reverse_equals_func(s: string)
    ensures reverse(s) == reverse_func(s)
{
}

lemma reverse_func_preserves_palindrome(s: string)
    requires is_palindrome(s)
    ensures reverse_func(s) == s
{
}

lemma reverse_func_append_palindrome(s: string)
    ensures is_palindrome(s + reverse_func(s))
{
}
// </vc-helpers>

// <vc-spec>
method reverse(str: string) returns (rev: string)
    // post-conditions-start
    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    result := s + reverse(s);
}
// </vc-code>

