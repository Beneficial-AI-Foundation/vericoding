function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}

// <vc-helpers>
function reverse_string(s: string): string
    decreases |s|
    ensures |reverse_string(s)| == |s|
    ensures forall k :: 0 <= k < |s| ==> reverse_string(s)[k] == s[|s| - 1 - k]
{
    if s == "" then ""
    else s[|s|-1] + reverse_string(s[0..|s|-1])
}
// </vc-helpers>

// <vc-spec>
method make_palindrome(s: string) returns (result: string)
    // post-conditions-start
    ensures |result| <= 2 * |s|
    ensures is_palindrome(result)
    ensures starts_with(result, s)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if s == "" {
        result := "";
    } else {
        result := s + reverse_string(s[0..|s|-1]);
    }
}
// </vc-code>

method reverse(str: string) returns (rev: string)
    // post-conditions-start
    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
    // post-conditions-end
{
  assume{:axiom} false;
}