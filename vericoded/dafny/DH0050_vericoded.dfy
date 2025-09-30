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
    invariant forall j :: 0 <= j < i ==> to_lower(text[j]) == to_lower(text[|text| - 1 - j])
  {
    if to_lower(text[i]) != to_lower(text[|text| - 1 - i]) {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>
