method remove_vowels(text : string) returns (s : string)
    // post-conditions-start
    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] != 'a' && s[i] != 'e' && s[i] != 'i' && s[i] != 'o' && s[i] != 'u'
    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] in text
    ensures forall j : int :: j >= 0 && j < |text| && text[j] != 'a' && text[j] != 'e' && text[j] != 'i' && text[j] != 'o' && text[j] != 'u' ==> text[j] in s
    // post-conditions-end
{
    // impl-start
    s := "";
    var i : int := 0;
    while (i < |text|)
        // invariants-start
        invariant 0 <= i && i <= |text|
        invariant forall i : int :: i >= 0 && i < |s| ==> s[i] != 'a' && s[i] != 'e' && s[i] != 'i' && s[i] != 'o' && s[i] != 'u'
        invariant forall i : int :: i >= 0 && i < |s| ==> s[i] in text
        invariant forall j : int :: j >= 0 && j < i && text[j] != 'a' && text[j] != 'e' && text[j] != 'i' && text[j] != 'o' && text[j] != 'u' ==> text[j] in s
        // invariants-end
    {
        var c : char := text[i];
        if (c != 'a' && c != 'e' && c != 'i' && c != 'o' && c != 'u')
        {
            s := s + [c];
        }
        i := i + 1;
    }
    // impl-end
}
