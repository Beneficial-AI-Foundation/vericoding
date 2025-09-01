

// <vc-helpers>
function rot2_char(c: char): char
  requires ('a' <= c <= 'z' || 'A' <= c <= 'Z')
  requires is_vowel(c)
{
  (c as int + 2) as char
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
{
  var charArray := new char[|s|];
  for i := 0 to |s| - 1
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> 
      (is_vowel(s[j]) ==> charArray[j] == rot2_char(swap_case(s[j]))) && 
      (!is_vowel(s[j]) ==> charArray[j] == swap_case(s[j]))
  {
    var original_char := s[i];
    var processed_char: char;

    if is_vowel(original_char)
    {
      processed_char := rot2_char(swap_case(original_char));
    }
    else
    {
      processed_char := swap_case(original_char);
    }
    
    charArray[i] := processed_char;
  }
  return new String(charArray);
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