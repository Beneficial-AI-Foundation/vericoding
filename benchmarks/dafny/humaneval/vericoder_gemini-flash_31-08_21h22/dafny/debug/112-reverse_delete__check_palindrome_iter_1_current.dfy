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
    ensures |temp_s| <= |s|
    ensures forall j :: 0 <= j < |temp_s| ==> temp_s[j] !in chars
    ensures forall j :: 0 <= j < |temp_s| ==> temp_s[j] in s
    ensures forall j :: 0 <= j < i && s[j] !in chars ==> s[j] in temp_s
  {
    if !(s[i] in chars)
    {
      temp_s := temp_s + s[i];
    }
  }
  res := temp_s;
  is_palindrome := is_palindrome_pred(res);
}
// </vc-code>

function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end