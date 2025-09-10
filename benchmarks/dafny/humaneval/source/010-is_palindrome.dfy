function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end
function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}
// pure-end
method make_palindrome(s: string) returns (result: string)
    // post-conditions-start
    ensures |result| <= 2 * |s|
    ensures is_palindrome(result)
    ensures starts_with(result, s)
    // post-conditions-end
{
    // impl-start
    if (|s| == 0) {
        return "";
    }

    var beginning_of_suffix := 0;
    var longest_palindrome := "";
    var flag := is_palindrome(s[beginning_of_suffix..]);

    while (!flag)
        // invariants-start
        invariant (beginning_of_suffix >= 0 && beginning_of_suffix + 1 < |s|) || (flag && (beginning_of_suffix >= 0 && beginning_of_suffix < |s|))
        decreases |s| - beginning_of_suffix
        invariant flag ==> is_palindrome(s[beginning_of_suffix..])
        // invariants-end
    {
        beginning_of_suffix := beginning_of_suffix + 1;
        flag := is_palindrome(s[beginning_of_suffix..]);
    }

    var prefix_to_reverse := s[..beginning_of_suffix];
    var reversed := reverse(prefix_to_reverse);
    result := s + reversed;
    // impl-end
}

method reverse(str: string) returns (rev: string)
    // post-conditions-start
    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
    // post-conditions-end
{
    // impl-start
    rev := "";
    for i := 0 to |str|
        // invariants-start
        invariant |rev| == i
        invariant forall k :: 0 <= k < i ==> rev[k] == str[|str| - 1 - k]
        // invariants-end
    {
        rev := rev + [str[|str| - i - 1]];
    }
    // impl-end
}
