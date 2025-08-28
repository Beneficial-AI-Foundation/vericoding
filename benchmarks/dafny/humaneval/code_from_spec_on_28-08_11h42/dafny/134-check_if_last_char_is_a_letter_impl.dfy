// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method check_if_last_char_is_a_letter(s: string) returns (b: bool)
  // post-conditions-start
  ensures b <==> |s| > 0 && is_alpha(s[|s| - 1]) && (|s| == 1 || s[|s| - 2] == ' ')
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| == 0 {
    return false;
  }
  
  var last_char := s[|s| - 1];
  
  if !is_alpha(last_char) {
    return false;
  }
  
  if |s| == 1 {
    return true;
  }
  
  var second_to_last := s[|s| - 2];
  return second_to_last == ' ';
}
// </vc-code>

function is_alpha(c: char) : bool {
    'a' <= c <= 'z' || 'A' <= c <= 'Z'
}
// pure-end