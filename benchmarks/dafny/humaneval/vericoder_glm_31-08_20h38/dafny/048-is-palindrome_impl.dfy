

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_palindrome(text : string) returns (result : bool)
    // post-conditions-start
    ensures result == (forall i : int :: i >= 0 && i < |text| ==> text[i] == text[|text| - i - 1])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var n := |text|;
    var i := 0;
    while i < n / 2
        invariant 0 <= i <= n/2
        invariant forall j : int :: 0 <= j < i ==> text[j] == text[n - j - 1]
    {
        if text[i] != text[n - i - 1] {
            return false;
        }
        i := i + 1;
    }
    return true;
}
// </vc-code>

