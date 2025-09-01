

// <vc-helpers>

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
  var i := 0;
  var hasAlpha := false;
  while i < |s| && !hasAlpha
    invariant 0 <= i <= |s|
    invariant hasAlpha == (exists k :: 0 <= k < i && is_alpha(s[k]))
  {
    if is_alpha(s[i]) {
      hasAlpha := true;
    }
    i := i + 1;
  }
  if hasAlpha {
    t := [for i in 0..|s| - 1 :: (if is_alpha(s[i]) then flip_case(s[i]) else s[i])];
  } else {
    t := [for i in 0..|s| - 1 :: s[|s| - 1 - i]];
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