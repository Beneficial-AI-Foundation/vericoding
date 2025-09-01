

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method check_if_last_char_is_a_letter(s: string) returns (b: bool)
  // post-conditions-start
  ensures b <==> |s| > 0 && is_alpha(s[|s| - 1]) && (|s| == 1 || s[|s| - 2] == ' ')
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| > 0 {
    var lastIndex := |s| - 1;
    var lastChar := s[lastIndex];
    b := is_alpha(lastChar) && (|s| == 1 || s[lastIndex - 1] == ' ');
  } else {
    b := false;
  }
}
// </vc-code>

function is_alpha(c: char) : bool {
    'a' <= c <= 'z' || 'A' <= c <= 'Z'
}
// pure-end