// <vc-helpers>
function IsVowel(c: char): bool
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
  c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

predicate HasNoVowels(s: string)
{
  forall i :: 0 <= i < |s| ==> !IsVowel(s[i])
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def remove_vowels(string: str) -> string
remove_vowels is a function that takes string and returns string without vowels.
*/
// </vc-description>

// <vc-spec>
method remove_vowels(s: string) returns (result: string)
  ensures HasNoVowels(result)
  ensures forall c :: c in result ==> c in s && !IsVowel(c)
  ensures forall i :: 0 <= i < |s| && !IsVowel(s[i]) ==> s[i] in result
// </vc-spec>
// <vc-code>
method remove_vowels(s: string) returns (result: string)
  ensures HasNoVowels(result)
  ensures forall c :: c in result ==> c in s && !IsVowel(c)
  ensures forall i :: 0 <= i < |s| && !IsVowel(s[i]) ==> s[i] in result
{
  result := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant HasNoVowels(result)
    invariant forall c :: c in result ==> c in s && !IsVowel(c)
    invariant forall j :: 0 <= j < i && !IsVowel(s[j]) ==> s[j] in result
  {
    if !IsVowel(s[i]) {
      result := result + [s[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
