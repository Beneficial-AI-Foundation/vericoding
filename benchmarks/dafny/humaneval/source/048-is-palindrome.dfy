method is_palindrome(text : string) returns (result : bool)
    // post-conditions-start
    ensures result == (forall i : int :: i >= 0 && i < |text| ==> text[i] == text[|text| - i - 1])
    // post-conditions-end
{
    // impl-start
    result := true;
    var i : int := 0;
    while i < |text| / 2
        // invariants-start
        invariant 0 <= i && i <= |text| / 2
        invariant result == (forall i1 : int :: i1 >= 0 && i1 < i ==> text[i1] == text[|text| - i1 - 1])
        // invariants-end
    {
        if text[i] != text[|text| - i - 1]
        {
            result := false;
        }
        i := i + 1;
    }
    // impl-end
}
