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
// No additional helpers needed for this task
// </vc-helpers>

// <vc-description>
/*
function_signature: method reverse(str: string) returns (rev: string)
Reverse order. Ensures: returns the correct size/count; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method reverse(str: string) returns (rev: string)
    requires true
    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
// </vc-spec>
// <vc-code>
{
    var n := |str|;
    rev := "";
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |rev| == i
        invariant forall k :: 0 <= k < i ==> rev[k] == str[n - 1 - k]
    {
        rev := rev + [str[n - 1 - i]];
        i := i + 1;
    }
}
// </vc-code>
