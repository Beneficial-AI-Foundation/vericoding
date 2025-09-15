// <vc-preamble>
function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// </vc-preamble>

// <vc-helpers>
function remove_chars(s: string, chars: string): string
{
  if |s| == 0 then ""
  else if s[0] in chars then remove_chars(s[1..], chars)
  else [s[0]] + remove_chars(s[1..], chars)
}

lemma remove_chars_properties(s: string, chars: string)
  ensures forall i :: 0 <= i < |remove_chars(s, chars)| ==> remove_chars(s, chars)[i] !in chars
  ensures forall i :: 0 <= i < |remove_chars(s, chars)| ==> remove_chars(s, chars)[i] in s
  ensures forall i :: 0 <= i < |s| && s[i] !in chars ==> s[i] in remove_chars(s, chars)
{
  if |s| == 0 {
  } else if s[0] in chars {
    remove_chars_properties(s[1..], chars);
  } else {
    remove_chars_properties(s[1..], chars);
  }
}
// </vc-helpers>

// <vc-spec>
method reverse_delete(s: string, chars: string) returns (res: string, is_palindrome: bool)

  ensures forall i :: 0 <= i < |res| ==> res[i] !in chars
  ensures forall i :: 0 <= i < |res| ==> res[i] in s
  ensures forall i :: 0 <= i < |s| && s[i] !in chars ==> s[i] in res
  ensures is_palindrome <==> is_palindrome_pred(res)
// </vc-spec>
// <vc-code>
{
  res := remove_chars(s, chars);
  remove_chars_properties(s, chars);
  is_palindrome := is_palindrome_pred(res);
}
// </vc-code>
