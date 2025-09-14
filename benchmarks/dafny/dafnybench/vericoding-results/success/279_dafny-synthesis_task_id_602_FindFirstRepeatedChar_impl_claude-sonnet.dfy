

// <vc-helpers>
lemma NoRepeatsUpTo(s: string, limit: int)
    requires 0 <= limit <= |s|
    requires forall i, j :: 0 <= i < j < limit ==> s[i] != s[j]
    ensures forall i, j :: 0 <= i < j < limit ==> s[i] != s[j]
{
}

lemma FirstRepeatProperty(s: string, pos: int, c: char)
    requires 0 <= pos < |s|
    requires s[pos] == c
    requires exists earlier :: 0 <= earlier < pos && s[earlier] == c
    requires forall i, j :: 0 <= i < j < pos ==> s[i] != s[j]
    ensures exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
{
    var earlier :| 0 <= earlier < pos && s[earlier] == c;
    assert s[earlier] == s[pos] && earlier < pos;
    assert forall k, l :: 0 <= k < l < pos && s[k] == s[l] ==> k >= earlier;
}
// </vc-helpers>

// <vc-spec>
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
    ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
    ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
// </vc-spec>
// <vc-code>
{
    found := false;
    c := if |s| > 0 then s[0] else 'a';
    
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall x, y :: 0 <= x < y < i ==> s[x] != s[y]
        invariant !found
    {
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant forall k :: 0 <= k < j ==> s[k] != s[i]
            invariant forall x, y :: 0 <= x < y < i ==> s[x] != s[y]
        {
            if s[j] == s[i] {
                found := true;
                c := s[i];
                FirstRepeatProperty(s, i, c);
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

