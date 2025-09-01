

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method is_palindrome(text : string) returns (result : bool)
    // post-conditions-start
    ensures result == (forall i : int :: i >= 0 && i < |text| ==> text[i] == text[|text| - i - 1])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    result := true;
    var i := 0;
    while i < |text| / 2 && result
        invariant 0 <= i <= |text| / 2
        invariant result ==> forall j :: 0 <= j < i ==> text[j] == text[|text| - 1 - j]
        decreases |text| - i
    {
        if text[i] != text[|text| - 1 - i] {
            result := false;
        }
        i := i + 1;
    }
}
// </vc-code>

