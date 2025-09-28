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

/* code modified by LLM (iteration 2): removed unprovable loop invariant and added aggregate at end to ensure postcondition */
{
  var i: int := 0;
  result := true;
  while i < |text| / 2
    invariant 0 <= i <= |text| / 2
    invariant forall k :: 0 <= k < i ==> to_lower(text[k]) == to_lower(text[|text| - 1 - k])
  {
    if to_lower(text[i]) != to_lower(text[|text| - 1 - i]) {
      result := false;
      break;
    }
    i := i + 1;
  }
  if result {
    assert IsPalindrome(text);
  }
}
// </vc-code>
