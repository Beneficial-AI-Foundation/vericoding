method reverse_delete(s: string, chars: string) returns (res: string, is_palindrome: bool)
  // post-conditions-start
  ensures forall i :: 0 <= i < |res| ==> res[i] !in chars
  ensures forall i :: 0 <= i < |res| ==> res[i] in s
  ensures forall i :: 0 <= i < |s| && s[i] !in chars ==> s[i] in res
  ensures is_palindrome <==> is_palindrome_pred(res)
  // post-conditions-end
{
  // impl-start
  res := "";
  var i := 0;
  while i < |s|
    // invariants-start
    invariant 0 <= i <= |s|
    invariant forall i :: 0 <= i < |res| ==> res[i] !in chars
    invariant forall i :: 0 <= i < |res| ==> res[i] in s
    invariant forall j :: 0 <= j < i && s[j] !in chars ==> s[j] in res
    // invariants-end
  {
    if s[i] !in chars {
      res := res + [s[i]];
    }
    i := i + 1;
  }

  is_palindrome := check_palindrome(res);
  // impl-end
}

method check_palindrome(s: string) returns (result: bool)
  // post-conditions-start
  ensures result <==> is_palindrome_pred(s)
  // post-conditions-end
{
  // impl-start
  if |s| == 0 {
    return true;
  }
  result := true;
  var i := 0;
  var j := |s| - 1;
  while (i < j)
    // invariants-start
    invariant 0 <= i < |s|
    invariant 0 <= j < |s|
    invariant j == |s| - i - 1
    invariant forall k :: 0 <= k < i ==> s[k] == s[|s| - 1 - k]
    // invariants-end
  {
    if (s[i] != s[j]) {
      result := false;
      break;
    }
    i := i + 1;
    j := j - 1;
  }
  // impl-end
}

function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end
