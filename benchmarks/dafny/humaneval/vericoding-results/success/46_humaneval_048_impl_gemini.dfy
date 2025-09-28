// <vc-preamble>

function to_lower(c: char): char
{
    if 'A' <= c <= 'Z' then
        (c as int - 'A' as int + 'a' as int) as char
    else
        c
}

predicate IsPalindrome(text: string)
{
    forall i :: 0 <= i < |text| ==> to_lower(text[i]) == to_lower(text[|text| - 1 - i])
}
// </vc-preamble>

// <vc-helpers>
lemma PalindromeSymmetry(s: string)
  ensures (forall k :: 0 <= k < |s| / 2 ==> to_lower(s[k]) == to_lower(s[|s| - 1 - k])) ==> IsPalindrome(s)
{
}
// </vc-helpers>

// <vc-spec>
method is_palindrome(text: string) returns (result: bool)
  ensures result <==> IsPalindrome(text)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < |text| / 2
    invariant 0 <= i <= |text| / 2
    invariant forall k :: 0 <= k < i ==> to_lower(text[k]) == to_lower(text[|text| - 1 - k])
  {
    if to_lower(text[i]) != to_lower(text[|text| - 1 - i]) {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
  PalindromeSymmetry(text);
}
// </vc-code>
