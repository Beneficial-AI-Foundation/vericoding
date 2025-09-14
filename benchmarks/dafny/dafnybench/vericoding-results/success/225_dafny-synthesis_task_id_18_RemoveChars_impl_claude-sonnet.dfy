

// <vc-helpers>
lemma CharInStringImpliesExists(s: string, c: char)
    requires c in s
    ensures exists i :: 0 <= i < |s| && s[i] == c
{
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> s[j] != c
    {
        if s[i] == c {
            return;
        }
        i := i + 1;
    }
}

predicate CharInString(c: char, s: string)
{
    exists i :: 0 <= i < |s| && s[i] == c
}

lemma CharInStringEquivalent(c: char, s: string)
    ensures CharInString(c, s) <==> (c in s)
{
    if CharInString(c, s) {
        assert c in s;
    }
    if c in s {
        CharInStringImpliesExists(s, c);
        assert CharInString(c, s);
    }
}
// </vc-helpers>

// <vc-spec>
method RemoveChars(s1: string, s2: string) returns (v: string)
    ensures |v| <= |s1|
    ensures forall i :: 0 <= i < |v| ==> (v[i] in s1) && !(v[i] in s2)
    ensures forall i :: 0 <= i < |s1| ==> (s1[i] in s2) || (s1[i] in v)
// </vc-spec>
// <vc-code>
{
    v := "";
    var i := 0;
    while i < |s1|
        invariant 0 <= i <= |s1|
        invariant |v| <= i
        invariant forall j :: 0 <= j < |v| ==> (v[j] in s1) && !(v[j] in s2)
        invariant forall j :: 0 <= j < i ==> (s1[j] in s2) || (s1[j] in v)
    {
        if !(s1[i] in s2) {
            v := v + [s1[i]];
        }
        i := i + 1;
    }
}
// </vc-code>

