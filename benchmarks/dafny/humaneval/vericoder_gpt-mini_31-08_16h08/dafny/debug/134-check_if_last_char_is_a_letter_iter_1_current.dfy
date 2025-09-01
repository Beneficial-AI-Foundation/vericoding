

// <vc-helpers>
// No helpers required for this verification
// </vc-helpers>

// <vc-spec>
method check_if_last_char_is_a_letter(s: string) returns (b: bool)
  // post-conditions-start
  ensures b <==> |s| > 0 && is_alpha(s[|s| - 1]) && (|s| == 1 || s[|s| - 2] == ' ')
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  if n == 0 {
    b := false;
  } else {
    var last := s[n - 1];
    if !is_alpha(last) {
      b := false;
    } else if n == 1 {
      b := true;
    } else {
      b := s[n - 2] == ' ';
    }
  }
}
// </vc-code>

function is_alpha(c: char) : bool {
    'a' <= c <= 'z' || 'A' <= c <= 'Z'
}
// pure-end