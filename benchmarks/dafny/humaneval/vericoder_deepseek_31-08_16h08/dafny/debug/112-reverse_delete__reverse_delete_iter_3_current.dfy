

// <vc-helpers>
function is_palindrome_pred_fn(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}

lemma palindrome_helper(s: string, left: int, right: int)
  requires 0 <= left <= right + 1 <= |s|
  requires forall k :: 0 <= k < left || right < k < |s| ==> s[k] == s[|s| - 1 - k]
  ensures forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k] || left <= k <= right
{
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
  var s1 := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall c :: c in s1 ==> c !in chars
    invariant forall idx :: 0 <= idx < |s1| ==> s1[idx] in s
    invariant forall idx :: 0 <= idx < i && s[idx] !in chars ==> s[idx] in s1
    invariant forall idx :: 0 <= idx < |s| && s[idx] !in chars ==> s[idx] in s1 || idx >= i
  {
    if s[i] !in chars {
      s1 := s1 + [s[i]];
    }
    i := i + 1;
  }
  
  res := s1;
  
  var left := 0;
  var right := |res| - 1;
  is_palindrome := true;
  
  while left < right
    invariant 0 <= left <= right + 1 <= |res|
    invariant is_palindrome ==> forall k :: 0 <= k < left || right < k < |res| ==> res[k] == res[|res| - 1 - k]
  {
    if res[left] != res[right] {
      is_palindrome := false;
      break;
    }
    left := left + 1;
    right := right - 1;
  }
  
  if is_palindrome {
    palindrome_helper(res, left, right);
  }
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