// <vc-preamble>
function is_alpha(c: char) : bool {
  'a' <= c <= 'z' || 'A' <= c <= 'Z'
}
// </vc-preamble>

// <vc-helpers>
lemma LastCharIfIsLetter(s: string, i: int, c: char)
  requires 0 <= i < |s|
  ensures i == |s| - 1 ==> s[i] == c ==> c == s[|s| - 1]
{
}
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
    if |s| > 1 {
      var second_last_char := s[|s| - 2];
      if is_alpha(last_char) && second_last_char == ' ' {
        b := true;
      } else {
        b := false;
      }
    } else {
      b := is_alpha(last_char);
    }
  }
}
// </vc-code>
