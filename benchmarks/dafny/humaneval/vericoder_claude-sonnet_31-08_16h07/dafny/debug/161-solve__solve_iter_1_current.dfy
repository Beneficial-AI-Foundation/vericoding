

// <vc-helpers>
lemma reverse_preserves_alpha(s: string, rev: string, i: int)
  requires |rev| == |s|
  requires forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  requires 0 <= i < |s|
  ensures is_alpha(s[i]) == is_alpha(rev[|s| - 1 - i])
{
}

lemma no_alpha_chars_preserved(s: string, rev: string)
  requires |rev| == |s|
  requires forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  requires forall i :: 0 <= i < |s| ==> !is_alpha(s[i])
  ensures forall i :: 0 <= i < |s| ==> !is_alpha(rev[i])
{
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
  if |s| == 0 {
    return s;
  }
  
  var has_alpha := false;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant has_alpha <==> (exists j :: 0 <= j < i && is_alpha(s[j]))
  {
    if is_alpha(s[i]) {
      has_alpha := true;
    }
    i := i + 1;
  }
  
  if !has_alpha {
    t := reverse(s);
  } else {
    t := "";
    i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant |t| == i
      invariant forall j :: 0 <= j < i ==> 
        if is_alpha(s[j]) then t[j] == flip_case(s[j]) else t[j] == s[j]
    {
      if is_alpha(s[i]) {
        t := t + [flip_case(s[i])];
      } else {
        t := t + [s[i]];
      }
      i := i + 1;
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