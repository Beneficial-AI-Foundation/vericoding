

// <vc-helpers>

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
    invariant forall j :: 0 <= j < |res| ==> res[j] !in chars
    invariant forall j :: 0 <= j < |res| ==> res[j] in s
    invariant forall j :: 0 <= j < i && s[j] !in chars ==> s[j] in res
  {
    if s[i] !in chars {
      res := res + [s[i]];
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