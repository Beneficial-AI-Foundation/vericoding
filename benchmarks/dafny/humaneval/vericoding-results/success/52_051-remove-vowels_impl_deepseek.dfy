// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed function syntax and corrected lemma syntax */
function isVowel(c: char): bool
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

lemma InStringAnimation(ch: char, s: string)
  ensures ch in s <==> (exists j | 0 <= j < |s| :: s[j] == ch)
{
}
// </vc-helpers>

// <vc-spec>
method remove_vowels(text : string) returns (s : string)

    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] != 'a' && s[i] != 'e' && s[i] != 'i' && s[i] != 'o' && s[i] != 'u'
    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] in text
    ensures forall j : int :: j >= 0 && j < |text| && text[j] != 'a' && text[j] != 'e' && text[j] != 'i' && text[j] != 'o' && text[j] != 'u' ==> text[j] in s
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed implementation to satisfy all ensures clauses */
{
  s := "";
  var i := 0;
  while i < |text|
    invariant 0 <= i <= |text|
    invariant forall k :: 0 <= k < |s| ==> !isVowel(s[k])
    invariant forall k :: 0 <= k < |s| ==> s[k] in text
    invariant forall j :: 0 <= j < i && !isVowel(text[j]) ==> text[j] in s
    invariant forall j :: 0 <= j < |text| && !isVowel(text[j]) ==> j < i ==> text[j] in s
  {
    if !isVowel(text[i]) {
      s := s + [text[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
