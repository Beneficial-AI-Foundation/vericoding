function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}

// <vc-helpers>
function reverse_string(str: string) : string
  ensures |reverse_string(str)| == |str|
  ensures forall k :: 0 <= k < |str| ==> reverse_string(str)[k] == str[|str| - 1 - k]
{
  if |str| == 0 then
    ""
  else
    reverse_string(str[1..]) + str[0..1]
}
// </vc-helpers>

// <vc-spec>
method make_palindrome(s: string) returns (result: string)
    // post-conditions-start
    ensures |result| <= 2 * |s|
    ensures is_palindrome(result)
    ensures starts_with(result, s)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    result := s + reverse_string(s[..|s|-1]);
    if is_palindrome(s) then
      result := s;
    else
      result := s + reverse_string(s[..|s|-1]);
    
    return result;
}
// </vc-code>

method reverse(str: string) returns (rev: string)
    // post-conditions-start
    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
    // post-conditions-end
{
  assume{:axiom} false;
}