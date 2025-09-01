

// <vc-helpers>
lemma lemma_last_char_condition(s: string)
  requires |s| > 0
  ensures (|s| == 1 || s[|s| - 2] == ' ') <==> (|s| - 1 == 0 || s[|s| - 2] == ' ')
{
}
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
    var last_char := s[|s| - 1];
    var is_letter := is_alpha(last_char);
    if is_letter {
      if |s| == 1 {
        b := true;
      } else {
        var prev_char := s[|s| - 2];
        b := prev_char == ' ';
      }
    } else {
      b := false;
    }
  }
}
// </vc-code>

function is_alpha(c: char) : bool {
    'a' <= c <= 'z' || 'A' <= c <= 'Z'
}
// pure-end