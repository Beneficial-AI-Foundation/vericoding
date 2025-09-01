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

lemma palindrome_append(s: string, c: char)
  requires is_palindrome_pred(s)
  ensures is_palindrome_pred([c] + s + [c])
{
}

lemma palindrome_append_left(s: string, c: char)
  requires is_palindrome_pred(s)
  ensures is_palindrome_pred([c] + s)
  decreases |s|
{
}

lemma palindrome_append_right(s: string, c: char)
  requires is_palindrome_pred(s)
  ensures is_palindrome_pred(s + [c])
  decreases |s|
{
}

predicate in_string(c: char, s: string) {
  exists i :: 0 <= i < |s| && s[i] == c
}

function is_palindrome_pred(s: string) : bool {
  if |s| == 0 then true
  else forall k :: 0 <= k < |s|/2 ==> s[k] == s[|s| - 1 - k]
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
  var n := |s|;
  var left := 0;
  var right := n - 1;
  result := true;
  
  while left < right
    invariant 0 <= left <= right + 1 <= n
    invariant left <= right + 1
    invariant forall k :: 0 <= k < left ==> s[k] == s[n - 1 - k]
    invariant result <==> (forall k :: 0 <= k < left ==> s[k] == s[n - 1 - k])
  {
    if s[left] != s[right] {
      result := false;
      return;
    }
    left := left + 1;
    right := right - 1;
  }
  if n > 0 {
    assert left >= right;
    assert forall k :: 0 <= k < |s|/2 ==> s[k] == s[n - 1 - k];
  }
}
// </vc-code>

function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end