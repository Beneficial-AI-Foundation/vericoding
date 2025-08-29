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
// </vc-helpers>

// <vc-description>
/*
function_signature: method reverse(str: string) returns (rev: string)
Reverse order. Ensures: returns the correct size/count; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method reverse(str: string) returns (rev: string)
    ensures |rev| == |str|
    ensures forall i :: 0 <= i < |str| ==> rev[i] == str[|str| - 1 - i]
// </vc-spec>
// <vc-code>
{
    rev := "";
    var i := |str|;
    while i > 0
        invariant 0 <= i <= |str|
        invariant |rev| == |str| - i
        invariant forall j :: 0 <= j < |rev| ==> rev[j] == str[|str| - 1 - j]
    {
        i := i - 1;
        rev := rev + [str[i]];
    }
}
// </vc-code>
