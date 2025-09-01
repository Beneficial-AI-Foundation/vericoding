

// <vc-helpers>
lemma swap_case_preserves_vowel(c: char)
  requires 'a' <= c <= 'z' || 'A' <= c <= 'Z'
  requires is_vowel(c)
  ensures is_vowel(swap_case(c)) {
  assert is_vowel(swap_case(c)) == is_vowel(c);
  assert is_vowel(c);
  assert is_vowel(swap_case(c));
}
// </vc-helpers>

// <vc-spec>
method encode(s: string) returns (t: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'
  // pre-conditions-end
  // post-conditions-start
  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| && is_vowel(s[i]) ==> t[i] == rot2(swap_case(s[i]))
  ensures forall i :: 0 <= i < |s| && !is_vowel(s[i]) ==> t[i] == swap_case(s[i])
  // post-conditions-end
// </vc-spec>
// <vc-code>
var t := "";
for i := 0 to |s| - 1 {
  if is_vowel(s[i]) {
    t := t + rot2(swap_case(s[i]));
  } else {
    t := t + swap_case(s[i]);
  }
}
return t;
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