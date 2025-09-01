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
function is_palindrome_pred(s : seq<char>) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}

function method ToSet<T>(s: seq<T>): set<T>
{
  set i | 0 <= i < |s| :: s[i]
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
  var temp_res := "";
  var set_chars: set<char> := ToSet(chars);
  for i := 0 to |s| - 1
    invariant |temp_res| <= i + 1
    invariant forall k :: 0 <= k < |temp_res| ==> temp_res[k] !in set_chars
    invariant forall k :: 0 <= k < |temp_res| ==> temp_res[k] in ToSet(s)
    invariant forall k :: 0 <= k < i && s[k] !in set_chars ==> s[k] in ToSet(temp_res)
  {
    if !(s[i] in set_chars) {
      temp_res := temp_res + s[i..i+1];
    }
  }

  var reversed_res := "";
  for i := |temp_res| - 1 downto 0
    invariant |reversed_res| <= |temp_res| - i
    invariant forall k :: 0 <= k < |reversed_res| ==> reversed_res[k] == temp_res[|temp_res| - 1 - k]
  {
    reversed_res := reversed_res + temp_res[i..i+1];
  }

  res := temp_res;
  is_palindrome := is_palindrome_pred(res);
}
// </vc-code>

function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end