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
function EqLower(c1: char, c2: char): bool
{
  to_lower(c1) == to_lower(c2)
}
// </vc-helpers>

// <vc-spec>
method is_palindrome(text: string) returns (result: bool)
  ensures result <==> IsPalindrome(text)
// </vc-spec>
// <vc-code>
{
  var n := |text|;
  var i := 0;
  var ok := true;
  var bad := 0;
  while i < n
    invariant 0 <= i <= n
    invariant ok ==> (forall j :: 0 <= j < i ==> to_lower(text[j]) == to_lower(text[n - 1 - j]))
    invariant !ok ==> (0 <= bad < i && to_lower(text[bad]) != to_lower(text[n - 1 - bad]))
  {
    if ok {
      if to_lower(text[i]) == to_lower(text[n - 1 - i]) {
        i := i + 1;
      } else {
        ok := false;
        bad := i;
        i := i + 1;
      }
    } else {
      i := i + 1;
    }
  }
  if ok {
    assert forall j :: 0 <= j < n ==> to_lower(text[j]) == to_lower(text[n - 1 - j]);
    assert IsPalindrome(text);
  } else {
    assert 0 <= bad < n && to_lower(text[bad]) != to_lower(text[n - 1 - bad]);
    assert exists j :: 0 <= j < n && to_lower(text[j]) != to_lower(text[n - 1 - j]);
    assert !IsPalindrome(text);
  }
  result := ok;
}
// </vc-code>
