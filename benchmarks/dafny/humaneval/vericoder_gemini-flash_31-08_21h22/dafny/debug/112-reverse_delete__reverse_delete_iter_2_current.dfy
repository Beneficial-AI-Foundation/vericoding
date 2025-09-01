

// <vc-helpers>
function is_char_in_string(char_to_find: char, s: string): bool
  reads s
  ensures is_char_in_string(char_to_find, s) == exists i :: 0 <= i < |s| && s[i] == char_to_find
{
  exists i :: 0 <= i < |s| && s[i] == char_to_find
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
    var new_s := "";
    for i := |s| - 1 downto 0
    {
        var c_s := s[i];
        if !is_char_in_string(c_s, chars) {
            new_s := new_s + c_s;
        }
    }
    res := new_s;
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