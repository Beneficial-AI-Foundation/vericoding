

// <vc-helpers>
function reverse(s: string): string
  decreases |s|
  ensures |result| == |s|
  ensures forall k :: 0 <= k < |s| ==> result[k] == s[|s|-1-k]
{
  if |s| == 0 then ""
  else reverse(s[1..]) + [s[0]]
}

function is_alpha(c: char) : bool {
  'a' <= c <= 'z' || 'A' <= c <= 'Z'
}

function flip_case(c: char): (flipped: char)
  requires is_alpha(c)
  ensures is_alpha(flipped)
{
  if 'a' <= c <= 'z' then c - 'a' + 'A' else c - 'A' + 'a'
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
  var has_alpha := false;
  for i := 0 to |s| - 1
    invariant true
  {
    if is_alpha(s[i]) {
      has_alpha := true;
      break;
    }
  }
  if !has_alpha {
    t := reverse(s);
  } else {
    t := [];
    for i := 0 to |s| - 1
      invariant |t| == i
      invariant forall k :: 0 <= k < i ==> if is_alpha(s[k]) then t[k] == flip_case(s[k]) else t[k] == s[k]
    {
      t := t + (if is_alpha(s[i]) then [flip_case(s[i])] else [s[i]]);
    }
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