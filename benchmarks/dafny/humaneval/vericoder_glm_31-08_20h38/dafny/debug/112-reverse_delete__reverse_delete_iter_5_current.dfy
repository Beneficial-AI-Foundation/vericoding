

// <vc-helpers>
function is_palindrome_pred(s: string): bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}

method check_palindrome(s: string) returns (result: bool)
  ensures result <==> is_palindrome_pred(s)
{
  var i := 0;
  var j := |s| - 1;
  result := true;
  while i < j
    invariant 0 <= i <= j <= |s|
    invariant result <==> is_palindrome_pred(s[i..j+1])
  {
    if s[i] != s[j] {
      result := false;
      break;
    }
    i := i + 1;
    j := j - 1;
  }
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
  var filtered := "";
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < |filtered| ==> filtered[j] !in chars
    invariant forall j :: 0 <= j < |filtered| ==> filtered[j] in s
    invariant forall j :: 0 <= j < i && s[j] !in chars ==> s[j] in filtered
  {
    if s[i] !in chars {
      filtered := filtered + [s[i]];
    }
    i := i + 1;
  }
  
  res := filtered;
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