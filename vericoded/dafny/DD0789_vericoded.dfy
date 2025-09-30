

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsDecimalWithTwoPrecision(s: string) returns (result: bool)
    ensures result ==> (exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
    ensures !result ==> !(exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> !(s[j] == '.' && |s| - j - 1 == 2)
    {
        if s[i] == '.' && |s| - i - 1 == 2 {
            return true;
        }
        i := i + 1;
    }
    return false;
}
// </vc-code>

