// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ContainsZ(s: string) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
// </vc-spec>
// <vc-code>
{
    result := false;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < i ==> s[k] != 'z' && s[k] != 'Z'
    {
        if s[i] == 'z' || s[i] == 'Z' {
            result := true;
            return;
        }
        i := i + 1;
    }
}
// </vc-code>
