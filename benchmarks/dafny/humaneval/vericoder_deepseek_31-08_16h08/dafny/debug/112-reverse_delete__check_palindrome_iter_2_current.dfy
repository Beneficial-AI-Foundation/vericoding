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
// </vc-helpers>

// <vc-spec>
method check_palindrome(s: string) returns (result: bool)
  // post-conditions-start
  ensures result <==> is_palindrome_pred(s)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var filtered := "";
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < |filtered| ==> !in_string(filtered[j], chars)
    invariant forall j :: 0 <= j < |filtered| ==> in_string(filtered[j], s)
    invariant forall j :: 0 <= j < i && !in_string(s[j], chars) ==> in_string(s[j], filtered)
    invariant |filtered| <= i
  {
    if !in_string(s[i], chars) {
      filtered := filtered + [s[i]];
    }
    i := i + 1;
  }
  
  result := filtered;
  is_palindrome := is_palindrome_pred(filtered);
}
// </vc-code>

function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end