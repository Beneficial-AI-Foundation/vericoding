// <vc-helpers>
// Helper function to check if a character is a letter
function IsAlpha(c: char): bool {
    'a' <= c <= 'z' || 'A' <= c <= 'Z'
}
// </vc-helpers>

// <vc-spec>
method check_if_last_char_is_a_letter(s: string) returns (b: bool)
  // post-conditions-start
  ensures b <==> |s| > 0 && is_alpha(s[|s| - 1]) && (|s| == 1 || s[|s| - 2] == ' ')
  // post-conditions-end
// </vc-spec>
// <vc-code>
method CheckIfLastCharIsALetter(s: string) returns (b: bool)
  ensures b <==> |s| > 0 && IsAlpha(s[|s| - 1]) && (|s| == 1 || s[|s| - 2] == ' ')
{
  if |s| == 0 {
    return false;
  }
  
  var lastChar := s[|s| - 1];
  var isLastAlpha := IsAlpha(lastChar);
  
  if |s| == 1 {
    return isLastAlpha;
  }
  
  var secondLastChar := s[|s| - 2];
  return isLastAlpha && secondLastChar == ' ';
}
// </vc-code>

function is_alpha(c: char) : bool {
    'a' <= c <= 'z' || 'A' <= c <= 'Z'
}
// pure-end