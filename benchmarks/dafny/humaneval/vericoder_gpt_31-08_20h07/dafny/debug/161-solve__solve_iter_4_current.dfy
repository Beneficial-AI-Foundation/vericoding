

// <vc-helpers>
function mapFlip(s: string): string
  ensures |mapFlip(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> (if is_alpha(s[i]) then mapFlip(s)[i] == flip_case(s[i]) else mapFlip(s)[i] == s[i])
  decreases |s|
{
  if |s| == 0 then s
  else mapFlip(s[..|s|-1]) + [if is_alpha(s[|s|-1]) then flip_case(s[|s|-1]) else s[|s|-1]]
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (t: string)
  // post-conditions-start 
  ensures |s| == |t|
  ensures (forall i :: 0 <= i < |s| ==> !is_alpha(s[i])) ==> (forall i :: 0 <= i < |s| ==> s[i] == t[|t| - 1 - i])
  ensures (exists i :: 0 <= i < |s| && is_alpha(s[i])) ==> 
    (forall i :: 0 <= i < |t| ==> if is_alpha(s[i]) then t[i] == flip_case(s[i]) else t[i] == s[i])
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if (exists i :: 0 <= i < |s| && is_alpha(s[i])) {
    t := mapFlip(s);
  } else {
    t := reverse(s);
  }
}
// </vc-code>

method reverse(s: string) returns (rev: string)
  // pre-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // pre-conditions-end
{
  assume{:axiom} false;
}
function is_alpha(c: char) : bool {
  'a' <= c <= 'z' || 'A' <= c <= 'Z'
}
// pure-end
function flip_case(c: char): (flipped: char)
  requires is_alpha(c)
  ensures is_alpha(flipped)
{
  if 'a' <= c <= 'z' then c - 'a' + 'A' else c - 'A' + 'a'
}
// pure-end