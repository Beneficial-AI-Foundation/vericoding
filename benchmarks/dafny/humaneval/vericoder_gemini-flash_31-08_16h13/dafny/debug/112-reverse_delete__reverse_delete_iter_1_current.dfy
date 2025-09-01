

// <vc-helpers>
function method IsCharInString(charToFind: char, s: string): bool
  reads s
  ensures IsCharInString(charToFind, s) <==> exists i :: 0 <= i < |s| && s[i] == charToFind
{
  exists i :: 0 <= i < |s| && s[i] == charToFind
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
  var temp_res := "";
  for i := 0 to |s| - 1
    ensures forall k :: 0 <= k < |temp_res| ==> temp_res[k] !in chars
    ensures forall k :: 0 <= k < |temp_res| ==> temp_res[k] in s
    ensures forall k :: 0 <= k < i && s[k] !in chars ==> s[k] in temp_res
  {
    if !IsCharInString(s[i], chars) {
      temp_res := temp_res + s[i];
    }
  }
  res := temp_res;
  is_palindrome := check_palindrome(res);
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