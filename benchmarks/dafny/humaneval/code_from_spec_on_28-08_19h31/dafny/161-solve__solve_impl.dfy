// <vc-helpers>
method ReverseString(s: string) returns (rev: string)
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
{
  var n := |s|;
  rev := "";
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |rev| == i
    invariant forall k :: 0 <= k < i ==> rev[k] == s[n - 1 - k]
  {
    rev := rev + [s[n - 1 - i]];
    i := i + 1;
  }
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
method Solve(s: string) returns (t: string)
  ensures |s| == |t|
  ensures (forall i :: 0 <= i < |s| ==> !is_alpha(s[i])) ==> (forall i :: 0 <= i < |s| ==> s[i] == t[|t| - 1 - i])
  ensures (exists i :: 0 <= i < |s| && is_alpha(s[i])) ==> 
    (forall i :: 0 <= i < |t| ==> if is_alpha(s[i]) then t[i] == flip_case(s[i]) else t[i] == s[i])
{
  var has_alpha := false;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant has_alpha ==> (exists k :: 0 <= k < i && is_alpha(s[k]))
  {
    if is_alpha(s[i]) {
      has_alpha := true;
    }
    i := i + 1;
  }
  
  if has_alpha {
    t := "";
    i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant |t| == i
      invariant forall k :: 0 <= k < i ==> (if is_alpha(s[k]) then t[k] == flip_case(s[k]) else t[k] == s[k])
    {
      if is_alpha(s[i]) {
        t := t + [flip_case(s[i])];
      } else {
        t := t + [s[i]];
      }
      i := i + 1;
    }
  } else {
    t := ReverseString(s);
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