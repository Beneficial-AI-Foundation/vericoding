

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
    b := false;
  } else {
    var last := s[|s| - 1];
    var prevSpace: bool;
    if |s| == 1 {
      prevSpace := true;
    } else {
      prevSpace := s[|s| - 2] == ' ';
    }
    b := is_alpha(last) && prevSpace;
  }
}
// </vc-code>

function is_alpha(c: char) : bool {
    'a' <= c <= 'z' || 'A' <= c <= 'Z'
}
// pure-end