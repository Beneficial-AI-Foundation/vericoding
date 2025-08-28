// <vc-helpers>
lemma DistinctCharsPrefix(s: string, end: int)
    requires 0 <= end <= |s|
    requires forall i, j :: 0 <= i < j < end ==> s[i] != s[j]
    ensures forall i :: 0 <= i < end ==> s[i] !in s[0..i]

lemma FirstRepeatedCharIsFirst(s: string, pos: int, c: char)
    requires 0 <= pos < |s|
    requires s[pos] == c
    requires c in s[0..pos]
    requires forall i, j :: 0 <= i < j < pos ==> s[i] != s[j]
    ensures exists first_pos :: 0 <= first_pos < pos && s[first_pos] == c &&
        (forall k, l :: 0 <= k < l < pos && s[k] == s[l] ==> k >= first_pos)
{
    var first_pos :| 0 <= first_pos < pos && s[first_pos] == c;
    if exists k, l :: 0 <= k < l < pos && s[k] == s[l] && k < first_pos {
        var k, l :| 0 <= k < l < pos && s[k] == s[l] && k < first_pos;
        DistinctCharsPrefix(s, pos);
        assert false;
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
    ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
    ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    found := false;
    c := if |s| > 0 then s[0] else 'a';
    
    for pos := 0 to |s|
        invariant forall i, j :: 0 <= i < j < pos ==> s[i] != s[j]
    {
        if s[pos] in s[0..pos] {
            found := true;
            c := s[pos];
            FirstRepeatedCharIsFirst(s, pos, c);
            return;
        }
    }
}
// </vc-code>
