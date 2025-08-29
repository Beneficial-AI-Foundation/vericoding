// <vc-helpers>
lemma SwapCasePreservesVowelProperty(c: char)
  requires 'a' <= c <= 'z' || 'A' <= c <= 'Z'
  ensures is_vowel(c) == is_vowel(swap_case(c))
{
  // This follows from the postcondition of swap_case
}

lemma Rot2ProducesValidChar(c: char)
  requires is_vowel(c)
  ensures 'a' <= rot2(c) <= 'z' || 'A' <= rot2(c) <= 'Z'
{
  // Since vowels are within valid ranges, rot2 produces valid chars
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def encode(s : str) -> str
Write a function that takes a message, and encodes in such a way that it swaps case of all letters, replaces all vowels in the message with the letter that appears 2 places ahead of that vowel in the english alphabet. Assume only letters.
*/
// </vc-description>

// <vc-spec>
method encode(s: string) returns (result: string)
  requires forall i :: 0 <= i < |s| ==> ('a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z')
  ensures |result| == |s|
  ensures forall i :: 0 <= i < |s| ==> ('a' <= result[i] <= 'z' || 'A' <= result[i] <= 'Z')
  ensures forall i :: 0 <= i < |s| && !is_vowel(s[i]) ==> result[i] == swap_case(s[i])
  ensures forall i :: 0 <= i < |s| && is_vowel(s[i]) ==> result[i] == rot2(swap_case(s[i]))
// </vc-spec>
// <vc-code>
{
  result := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> ('a' <= result[j] <= 'z' || 'A' <= result[j] <= 'Z')
    invariant forall j :: 0 <= j < i && !is_vowel(s[j]) ==> result[j] == swap_case(s[j])
    invariant forall j :: 0 <= j < i && is_vowel(s[j]) ==> result[j] == rot2(swap_case(s[j]))
  {
    var swapped := swap_case(s[i]);
    var encoded_char := if is_vowel(s[i]) then rot2(swapped) else swapped;
    result := result + [encoded_char];
    i := i + 1;
  }
}
// </vc-code>

function swap_case(c: char): char
  // pre-conditions-start
  requires 'a' <= c <= 'z' || 'A' <= c <= 'Z'
  // pre-conditions-end
  // post-conditions-start
  ensures 'a' <= c <= 'z' ==> 'A' <= swap_case(c) <= 'Z'
  ensures 'A' <= c <= 'Z' ==> 'a' <= swap_case(c) <= 'z'
  ensures is_vowel(swap_case(c)) == is_vowel(c)
  // post-conditions-end
{
  // impl-start
  if 'a' <= c <= 'z' then
    'A' + (c - 'a')
  else
    'a' + (c - 'A')
  // impl-end
}
// pure-end
function rot2(c: char): char
  requires is_vowel(c)
{
    (c as int + 2) as char
}
// pure-end
function is_vowel(c: char) : bool {
    (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u')
    || (c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U')
}
// pure-end