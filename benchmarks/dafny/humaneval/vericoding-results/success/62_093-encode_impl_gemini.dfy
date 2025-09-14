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
/* helper modified by LLM (iteration 3): no changes */
function encode_char(c: char): char
  requires 'a' <= c <= 'z' || 'A' <= c <= 'Z'
{
  if is_vowel(c) then 
    rot2(swap_case(c))
  else 
    swap_case(c)
}
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
  /* code modified by LLM (iteration 3): fix array length syntax from |t_arr| to t_arr.Length */
  var t_arr := new char[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant t_arr.Length == |s|
    invariant forall k :: 0 <= k < i ==> t_arr[k] == encode_char(s[k])
  {
    t_arr[i] := encode_char(s[i]);
    i := i + 1;
  }
  t := t_arr[..];
}
// </vc-code>
