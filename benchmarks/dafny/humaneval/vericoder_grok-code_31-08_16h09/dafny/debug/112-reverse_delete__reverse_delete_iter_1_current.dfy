

// <vc-helpers>
method check_if_palindrome(s: string) returns (b: bool)
  ensures b <==> is_palindrome_pred(s)
{
  var i := 0;
  var j := |s| - 1;
  while i < j
    invariant 0 <= i <= j + 1
    invariant j < |s|
    invariant forall k :: 0 <= k < i ==> s[k] == s[|s| - 1 - k]
  {
    if s[i] != s[j] {
      return false;
    }
    i := i + 1;
    j := j - 1;
  }
  return true;
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
  var res_seq : seq<char> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < |res_seq| ==> res_seq[k] !in chars && res_seq[k] in s
    invariant forall k :: 0 <= k < i && s[k] !in chars ==> s[k] in res_seq
  {
    if !(s[i] in chars) {
      res_seq := res_seq + [s[i]];
    }
    i := i + 1;
  }
  res := res_seq;
  is_palindrome := check_if_palindrome(res);
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