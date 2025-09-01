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
function is_palindrome_pred(s: string): bool
{
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
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
  var temp_s := "";
  for i := 0 to |s| - 1
  {
    if !(s[i] in chars.ToSet())
    {
      temp_s := temp_s + s[i];
    }
  }
  var res_local := temp_s;
  var is_palindrome_local := is_palindrome_pred(res_local);
  res := res_local;
  is_palindrome := is_palindrome_local;
}
// </vc-code>

function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end