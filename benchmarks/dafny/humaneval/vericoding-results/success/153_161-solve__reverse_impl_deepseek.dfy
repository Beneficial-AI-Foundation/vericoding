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
/* helper modified by LLM (iteration 3): Simplify helpers and add proper reversing function */
function reverse_string(s: string): string
  ensures |reverse_string(s)| == |s|
  ensures forall k :: 0 <= k < |s| ==> reverse_string(s)[k] == s[|s| - 1 - k]
{
  if |s| == 0 then
    s
  else
    reverse_string(s[1..]) + [s[0]]
}

predicate is_reversed(s: string, rev: string)
{
  |s| == |rev| && (forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k])
}
// </vc-helpers>

// <vc-spec>
method reverse(s: string) returns (rev: string)

  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Use proper reversing function implementation */
{
  rev := reverse_string(s);
}
// </vc-code>
