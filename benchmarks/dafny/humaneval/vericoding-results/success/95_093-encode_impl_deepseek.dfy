// <vc-preamble>
function swap_case(c: char): char

  requires 'a' <= c <= 'z' || 'A' <= c <= 'Z'

  ensures 'a' <= c <= 'z' ==> 'A' <= swap_case(c) <= 'Z'
  ensures 'A' <= c <= 'Z' ==> 'a' <= swap_case(c) <= 'z'
  ensures is_vowel(swap_case(c)) == is_vowel(c)

{

  if 'a' <= c <= 'z' then
    'A' + (c - 'a')
  else
    'a' + (c - 'A')

}
function rot2(c: char): char
  requires is_vowel(c)
{
    (c as int + 2) as char
}
function is_vowel(c: char) : bool {
    (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u')
    || (c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U')
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method encode(s: string) returns (t: string)

  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'

  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| && is_vowel(s[i]) ==> t[i] == rot2(swap_case(s[i]))
  ensures forall i :: 0 <= i < |s| && !is_vowel(s[i]) ==> t[i] == swap_case(s[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Remove duplicate helper functions from vc-helpers section */
  t := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |t| == i
    invariant forall j :: 0 <= j < i && is_vowel(s[j]) ==> t[j] == rot2(swap_case(s[j]))
    invariant forall j :: 0 <= j < i && !is_vowel(s[j]) ==> t[j] == swap_case(s[j])
  {
    if is_vowel(s[i]) {
      t := t + [rot2(swap_case(s[i]))];
    } else {
      t := t + [swap_case(s[i])];
    }
    i := i + 1;
  }
}
// </vc-code>
