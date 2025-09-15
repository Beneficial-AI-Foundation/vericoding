// <vc-preamble>
function is_alpha(c: char) : bool {
  'a' <= c <= 'z' || 'A' <= c <= 'Z'
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method check_if_last_char_is_a_letter(s: string) returns (b: bool)

  ensures b <==> |s| > 0 && is_alpha(s[|s| - 1]) && (|s| == 1 || s[|s| - 2] == ' ')
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed compilation error */
{
  if |s| == 0 {
    b := false;
  } else {
    var lastCharIsLetter: bool := is_alpha(s[|s| - 1]);
    if |s| == 1 {
      b := lastCharIsLetter;
    } else {
      var secondLastCharIsSpace: bool := s[|s| - 2] == ' ';
      b := lastCharIsLetter && secondLastCharIsSpace;
    }
  }
}
// </vc-code>
