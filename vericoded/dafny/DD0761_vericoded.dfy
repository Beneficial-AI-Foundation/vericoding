

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
    ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
    ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
// </vc-spec>
// <vc-code>
{
    found := false;
    c := '\0';  // dummy value
    var seen: set<char> := {};
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant seen == set j | 0 <= j < i :: s[j]
        invariant !found
        invariant forall j, k :: 0 <= j < k < i ==> s[j] != s[k]
    {
        if s[i] in seen {
            found := true;
            c := s[i];
            return;
        }
        seen := seen + {s[i]};
        i := i + 1;
    }
}
// </vc-code>

