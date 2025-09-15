// <vc-preamble>
function is_alpha(c: char) : bool {
  'a' <= c <= 'z' || 'A' <= c <= 'Z'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replaced invalid 'function method' with executable 'function' matching the ensures condition */
function LastCharCondition(s: string): bool {
  |s| > 0 && is_alpha(s[|s| - 1]) && (|s| == 1 || s[|s| - 2] == ' ')
}
// </vc-helpers>

// <vc-spec>
method check_if_last_char_is_a_letter(s: string) returns (b: bool)

  ensures b <==> |s| > 0 && is_alpha(s[|s| - 1]) && (|s| == 1 || s[|s| - 2] == ' ')
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement by delegating to helper function that matches the ensures condition */
  b := LastCharCondition(s);
}
// </vc-code>
