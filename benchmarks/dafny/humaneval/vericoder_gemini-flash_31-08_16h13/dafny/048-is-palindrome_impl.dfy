

// <vc-helpers>
function reverse_string(s: string): string
  ensures |reverse_string(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> reverse_string(s)[i] == s[|s| - 1 - i]
{
  if |s| == 0 then
    ""
  else
    reverse_string(s[1..]) + s[0..1]
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
  result := text == reverse_string(text);
}
// </vc-code>

