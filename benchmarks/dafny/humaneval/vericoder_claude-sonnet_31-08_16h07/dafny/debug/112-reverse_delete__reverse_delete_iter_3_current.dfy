

// <vc-helpers>
lemma palindrome_empty()
  ensures is_palindrome_pred("")
{
}

lemma palindrome_single(c: char)
  ensures is_palindrome_pred([c])
{
}

lemma filter_chars_preserves_order(s: string, chars: string, i: nat)
  requires i <= |s|
  ensures filter_chars(s[..i], chars) <= filter_chars(s, chars)
{
  if i == 0 {
  } else if s[0] in chars {
    filter_chars_preserves_order(s[1..], chars, i-1);
  } else {
    filter_chars_preserves_order(s[1..], chars, i-1);
  }
}

lemma filter_chars_incremental(s: string, chars: string, i: nat)
  requires i < |s|
  ensures if s[i] !in chars then filter_chars(s[..i+1], chars) == filter_chars(s[..i], chars) + [s[i]]
          else filter_chars(s[..i+1], chars) == filter_chars(s[..i], chars)
{
  if i == 0 {
  } else {
    filter_chars_incremental(s[1..], chars, i-1);
  }
}

function filter_chars(s: string, chars: string): string
{
  if |s| == 0 then ""
  else if s[0] in chars then filter_chars(s[1..], chars)
  else [s[0]] + filter_chars(s[1..], chars)
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
  res := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < |res| ==> res[j] !in chars
    invariant forall j :: 0 <= j < |res| ==> res[j] in s
    invariant forall j :: 0 <= j < i && s[j] !in chars ==> s[j] in res
    invariant res == filter_chars(s[..i], chars)
  {
    if s[i] !in chars {
      res := res + [s[i]];
    }
    filter_chars_incremental(s, chars, i);
    i := i + 1;
  }
  
  is_palindrome := true;
  i := 0;
  while i < |res| / 2 && is_palindrome
    invariant 0 <= i <= |res| / 2
    invariant is_palindrome ==> (forall k :: 0 <= k < i ==> res[k] == res[|res| - 1 - k])
    invariant !is_palindrome ==> !is_palindrome_pred(res)
    decreases |res| / 2 - i
  {
    if res[i] != res[|res| - 1 - i] {
      is_palindrome := false;
    } else {
      i := i + 1;
    }
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