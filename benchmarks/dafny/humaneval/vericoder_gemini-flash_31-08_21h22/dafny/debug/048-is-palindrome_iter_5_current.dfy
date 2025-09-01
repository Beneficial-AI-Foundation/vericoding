

// <vc-helpers>
function is_palindrome_recursive(text: string, start: int, end: int): bool
  decreases end - start
  requires start >= 0
  requires end < |text|
  requires start <= end + 1 // Added this to prevent out-of-bounds access when start > end
{
  if start >= end then
    true
  else if text[start] != text[end] then
    false
  else
    is_palindrome_recursive(text, start + 1, end - 1)
}
// </vc-helpers>

// <vc-spec>
method is_palindrome(text : string) returns (result : bool)
    // post-conditions-start
    ensures result == (forall i : int :: i >= 0 && i < |text| ==> text[i] == text[|text| - i - 1])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |text| == 0 then
    return true
  else if |text| == 1 then
    return true
  else
    return is_palindrome_recursive(text, 0, |text| - 1);
}
// </vc-code>

