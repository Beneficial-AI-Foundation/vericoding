// <vc-preamble>
function is_alpha(c: char) : bool {
  'a' <= c <= 'z' || 'A' <= c <= 'Z'
}
function flip_case(c: char): (flipped: char)
  requires is_alpha(c)
  ensures is_alpha(flipped)
{
  if 'a' <= c <= 'z' then c - 'a' + 'A' else c - 'A' + 'a'
}
// </vc-preamble>

// <vc-helpers>
function reverse_string(s: string): string {
  seq(|s|, i requires 0 <= i < |s| => s[|s|-1-i])
}
// </vc-helpers>

// <vc-spec>
method reverse(s: string) returns (rev: string)

  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
// </vc-spec>
// <vc-code>
{
  rev := reverse_string(s);
}
// </vc-code>
