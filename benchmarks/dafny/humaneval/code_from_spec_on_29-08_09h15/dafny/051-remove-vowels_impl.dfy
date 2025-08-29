

// <vc-helpers>
predicate is_vowel(c: char)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

lemma preserve_non_vowels_in_result(text: string, s: string, i: int)
    requires i >= 0 && i < |text|
    requires !is_vowel(text[i])
    requires forall j :: j >= 0 && j < |text| && !is_vowel(text[j]) ==> text[j] in s
    ensures text[i] in s
{
}

lemma result_chars_from_input(text: string, result: seq<char>, i: int)
    requires i >= 0 && i < |result|
    requires forall j :: j >= 0 && j < |result| ==> result[j] in text
    ensures result[i] in text
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def remove_vowels(string: str) -> string
remove_vowels is a function that takes string and returns string without vowels.
*/
// </vc-description>

// <vc-spec>
method remove_vowels(text : string) returns (s : string)
    // post-conditions-start
    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] != 'a' && s[i] != 'e' && s[i] != 'i' && s[i] != 'o' && s[i] != 'u'
    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] in text
    ensures forall j : int :: j >= 0 && j < |text| && text[j] != 'a' && text[j] != 'e' && text[j] != 'i' && text[j] != 'o' && text[j] != 'u' ==> text[j] in s
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    s := "";
    var i := 0;
    
    while i < |text|
        invariant 0 <= i <= |text|
        invariant forall j :: 0 <= j < |s| ==> !is_vowel(s[j])
        invariant forall j :: 0 <= j < |s| ==> s[j] in text
        invariant forall j :: 0 <= j < i && !is_vowel(text[j]) ==> text[j] in s
    {
        if !is_vowel(text[i]) {
            s := s + [text[i]];
        }
        i := i + 1;
    }
}
// </vc-code>

