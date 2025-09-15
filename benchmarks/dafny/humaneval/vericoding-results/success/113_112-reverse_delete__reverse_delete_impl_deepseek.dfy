// <vc-preamble>
function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// </vc-preamble>

// <vc-helpers>
function removeChars(s: string, chars: string): string
  ensures |removeChars(s, chars)| <= |s|
  ensures forall i :: 0 <= i < |removeChars(s, chars)| ==> removeChars(s, chars)[i] !in chars
  ensures forall i :: 0 <= i < |removeChars(s, chars)| ==> removeChars(s, chars)[i] in s
  ensures forall i :: 0 <= i < |s| && s[i] !in chars ==> s[i] in removeChars(s, chars)
{
  if |s| == 0 then
    ""
  else if s[0] in chars then
    removeChars(s[1..], chars)
  else
    [s[0]] + removeChars(s[1..], chars)
}

function isPalindrome(s: string): bool {
  if |s| <= 1 then
    true
  else
    s[0] == s[|s|-1] && isPalindrome(s[1..|s|-1])
}

/* helper modified by LLM (iteration 2): Added proper lemma to prove palindrome equivalence */
lemma palindromeEquivalence(s: string)
  ensures isPalindrome(s) <==> is_palindrome_pred(s)
{
  if |s| <= 1 {
  } else {
    palindromeEquivalence(s[1..|s|-1]);
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
/* code modified by LLM (iteration 2): Added lemma invocation to prove postcondition */
{
  var filtered := removeChars(s, chars);
  res := filtered;
  palindromeEquivalence(res);
  is_palindrome := isPalindrome(res);
}
// </vc-code>
