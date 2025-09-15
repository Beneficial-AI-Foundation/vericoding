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
{
  if |s| == 0 {
    b := false;
  } else {
    var last_char := s[|s| - 1];
    if !is_alpha(last_char) {
      b := false;
    } else if |s| == 1 {
      b := true;
    } else {
      var second_last := s[|s| - 2];
      b := (second_last == ' ');
    }
  }
}
// </vc-code>
