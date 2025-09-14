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
function method contains(c: char, s: string): bool
{
  exists i :: 0 <= i < |s| && s[i] == c
}

lemma contains_definition(c: char, s: string)
  ensures contains(c, s) <==> (exists i :: 0 <= i < |s| && s[i] == c)
{
}

function filter_out(s: string, chars: string): string
{
  if |s| == 0 then ""
  else if contains(s[0], chars) then filter_out(s[1..], chars)
  else [s[0]] + filter_out(s[1..], chars)
}

lemma filter_out_properties(s: string, chars: string)
  ensures forall i :: 0 <= i < |filter_out(s, chars)| ==> filter_out(s, chars)[i] !in chars
  ensures forall i :: 0 <= i < |filter_out(s, chars)| ==> filter_out(s, chars)[i] in s
  ensures forall i :: 0 <= i < |s| && s[i] !in chars ==> s[i] in filter_out(s, chars)
{
  if |s| == 0 {
  } else if contains(s[0], chars) {
    filter_out_properties(s[1..], chars);
  } else {
    filter_out_properties(s[1..], chars);
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
  var i := 0;
  var j := |s| - 1;
  result := true;
  
  while i < j
    invariant 0 <= i <= |s|
    invariant -1 <= j < |s|
    invariant i + j == |s| - 1
    invariant result <==> (forall k :: 0 <= k < i ==> s[k] == s[|s| - 1 - k])
  {
    if s[i] != s[j] {
      result := false;
      break;
    }
    i := i + 1;
    j := j - 1;
  }
}
// </vc-code>

function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end