

// <vc-helpers>
// no helpers needed
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
  res := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < |res| ==> res[k] !in chars
    invariant forall k :: 0 <= k < |res| ==> exists j :: 0 <= j < i && res[k] == s[j]
    invariant forall j :: 0 <= j < i && s[j] !in chars ==> (exists k :: 0 <= k < |res| && res[k] == s[j])
  {
    if s[i] !in chars {
      var oldRes := res;
      res := s[i..i+1] + oldRes;
      // prove that the newly prepended character is s[i]
      assert res[0] == s[i];
      // prove the remainder of res corresponds to old shifted by 1
      assert forall kk :: 1 <= kk < |res| ==> res[kk] == oldRes[kk-1];
      // prove that all characters in the new res are not in chars
      assert forall k :: 0 <= k < |res| ==>
               (if k == 0 then res[k] !in chars else oldRes[k-1] !in chars);
      // using the previous invariant about old, show old elements still appear in new res at shifted positions
      assert forall j :: 0 <= j < i && s[j] !in chars ==>
               (exists k :: 1 <= k < |res| && res[k] == s[j]);
      // and the current character s[i] appears (at position 0)
      assert exists k :: 0 <= k < |res| && res[k] == s[i];
    }
    i := i + 1;
  }
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