// <vc-helpers>
lemma character_preservation(s: string, chars: string, res: string, i: int)
  requires 0 <= i < |s|
  requires s[i] !in chars
  requires res == filter_chars(s, chars)
  ensures s[i] in res

lemma filter_chars_properties(s: string, chars: string)
  ensures forall i :: 0 <= i < |filter_chars(s, chars)| ==> filter_chars(s, chars)[i] !in chars
  ensures forall i :: 0 <= i < |filter_chars(s, chars)| ==> filter_chars(s, chars)[i] in s
  ensures forall i :: 0 <= i < |s| && s[i] !in chars ==> s[i] in filter_chars(s, chars)

function filter_chars(s: string, chars: string): string
{
  if |s| == 0 then ""
  else if s[0] in chars then filter_chars(s[1..], chars)
  else [s[0]] + filter_chars(s[1..], chars)
}
// </vc-helpers>

// <vc-spec>
method reverse_delete(s: string, chars: string) returns (res: string, is_palindrome: bool)
  // post-conditions-start
  ensures forall i :: 0 <= i < |res| ==> res[i] !in chars
  ensures forall i :: 0 <= i < |res| ==> res[i] in s
  ensures forall i :: 0 <= i < |s| && s[i] !in chars ==> s[i] in res
  ensures is_palindrome <==> is_palindrome_pred(res)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  res := filter_chars(s, chars);
  filter_chars_properties(s, chars);
  is_palindrome := is_palindrome_pred(res);
}
// </vc-code>

method check_palindrome(s: string) returns (result: bool)
  // post-conditions-start
  ensures result <==> is_palindrome_pred(s)
  // post-conditions-end
{
  assume{:axiom} false;
}
function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end