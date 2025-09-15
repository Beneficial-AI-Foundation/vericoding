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
  /* code modified by LLM (iteration 2): implement with while loop and invariants to prove postconditions */
  var result: seq<char> := [];
  var i := 0;
  while i < |s|
    invariant i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i && is_vowel(s[j]) ==> result[j] == rot2(swap_case(s[j]))
    invariant forall j :: 0 <= j < i && !is_vowel(s[j]) ==> result[j] == swap_case(s[j])
    decreases |s| - i
  {
    var c := s[i];
    if is_vowel(c) {
      result := result + [rot2(swap_case(c))];
    } else {
      result := result + [swap_case(c)];
    }
    i := i + 1;
  }
  t := result;
}
// </vc-code>
