method reverse_delete(s: string, chars: string) returns (res: string, is_palindrome: bool)
  // post-conditions-start
  ensures forall i :: 0 <= i < |res| ==> res[i] !in chars
  ensures forall i :: 0 <= i < |res| ==> res[i] in s
  ensures forall i :: 0 <= i < |s| && s[i] !in chars ==> s[i] in res
  ensures is_palindrome <==> is_palindrome_pred(res)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma palindrome_empty()
  ensures is_palindrome_pred("")
{
}

lemma palindrome_single(c: char)
  ensures is_palindrome_pred([c])
{
}

lemma palindrome_check_helper(s: string, i: int, j: int)
  requires 0 <= i <= j < |s|
  requires forall k :: i <= k <= j ==> s[k] == s[j - k + i]
  ensures forall k :: i <= k <= j ==> s[k] == s[|s| - 1 - k] || s[k] == s[|s| - 1 - (j - k + i)]
{
}
// </vc-helpers>

// <vc-spec>
method check_palindrome(s: string) returns (result: bool)
  // post-conditions-start
  ensures result <==> is_palindrome_pred(s)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| == 0 {
    result := true;
    return;
  }
  
  if |s| == 1 {
    result := true;
    return;
  }
  
  var i := 0;
  var j := |s| - 1;
  
  while i < j
    invariant 0 <= i <= j < |s|
    invariant forall k :: 0 <= k < i ==> s[k] == s[|s| - 1 - k]
    invariant i + j == |s| - 1
  {
    if s[i] != s[j] {
      result := false;
      return;
    }
    i := i + 1;
    j := j - 1;
  }
  
  result := true;
}
// </vc-code>

function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end