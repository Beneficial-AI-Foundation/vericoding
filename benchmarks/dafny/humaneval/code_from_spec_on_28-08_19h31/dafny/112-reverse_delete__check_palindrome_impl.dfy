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
function filter_string(s: string, c: string): string {
  if |s| == 0 then "" 
  else if s[0] in c then filter_string(s[1..], c)
  else s[..1] + filter_string(s[1..], c)
}

lemma FilterPreservesMembership(s: string, c: string)
  ensures forall i :: 0 <= i < |filter_string(s, c)| ==> filter_string(s, c)[i] in s
  ensures forall i :: 0 <= i < |filter_string(s, c)| ==> filter_string(s, c)[i] !in c
  ensures forall i :: 0 <= i < |s| && s[i] !in c ==> s[i] in filter_string(s, c)
{
  if |s| == 0 {
  } else {
    if s[0] in c {
      FilterPreservesMembership(s[1..], c);
    } else {
      FilterPreservesMembership(s[1..], c);
    }
  }
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
  var filtered := filter_string(s, chars);
  var len := |filtered|;
  var i := 0;
  var isPal := true;
  while i < len / 2
    invariant 0 <= i <= len / 2
    invariant isPal ==> forall k :: 0 <= k < i ==> filtered[k] == filtered[len - 1 - k]
  {
    if filtered[i] != filtered[len - 1 - i] {
      isPal := false;
      break;
    }
    i := i + 1;
  }
  return filtered, isPal;
}
// </vc-code>

function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end