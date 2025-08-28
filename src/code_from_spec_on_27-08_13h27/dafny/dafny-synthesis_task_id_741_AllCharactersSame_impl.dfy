// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method AllCharactersSame(s: string) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
    ensures !result ==> (|s| > 1) && (exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j])
// </vc-spec>
// </vc-spec>

// <vc-code>
method AllCharactersSameImpl(s: string) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
    ensures !result ==> (|s| > 1) && (exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j])
{
    if |s| == 0 || |s| == 1 {
        return true;
    }
    
    var firstChar := s[0];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < i ==> s[k] == firstChar
    {
        if s[i] != firstChar {
            return false;
        }
        i := i + 1;
    }
    return true;
}
// </vc-code>
