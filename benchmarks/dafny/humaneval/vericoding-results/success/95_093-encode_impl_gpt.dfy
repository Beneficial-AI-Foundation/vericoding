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
predicate IsAlpha(c: char) { ('a' <= c <= 'z') || ('A' <= c <= 'Z') }
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
  var a := new char[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i && is_vowel(s[j]) ==> a[j] == rot2(swap_case(s[j]))
    invariant forall j :: 0 <= j < i && !is_vowel(s[j]) ==> a[j] == swap_case(s[j])
    decreases |s| - i
  {
    var c := s[i];
    if is_vowel(c) {
      var sc := swap_case(c);
      assert is_vowel(sc) == is_vowel(c);
      a[i] := rot2(sc);
    } else {
      a[i] := swap_case(c);
    }
    i := i + 1;
  }
  t := a[..];
}
// </vc-code>
