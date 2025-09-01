

// <vc-helpers>
lemma reverse_properties(s: string, rev: string)
  requires |rev| == |s|
  requires forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  ensures forall i :: 0 <= i < |s| ==> s[i] == rev[|rev| - 1 - i]
{
}

lemma flip_case_involution(c: char)
  requires is_alpha(c)
  ensures flip_case(flip_case(c)) == c
{
}

lemma flip_case_preserves_boundaries(c: char)
  requires is_alpha(c)
  ensures 'a' <= flip_case(c) <= 'z' || 'A' <= flip_case(c) <= 'Z'
  ensures is_alpha(flip_case(c))
{
}

method reverse_impl(s: string) returns (rev: string)
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
{
  var chars := [];  // Start with empty sequence
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |chars| == i
    invariant forall k :: 0 <= k < i ==> chars[k] == s[|s| - 1 - k]
  {
    chars := chars + [s[|s| - 1 - i]];
    i := i + 1;
  }
  rev := chars;  // Sequence can be directly assigned to string
}
// </vc-helpers>
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
  var no_alpha := true;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant no_alpha ==> (forall j :: 0 <= j < i ==> !is_alpha(s[j]))
  {
    if is_alpha(s[i]) {
      no_alpha := false;
    }
    i := i + 1;
  }
  
  if no_alpha {
    var rev := reverse_impl(s);
    t := rev;
    reverse_properties(s, t);
  } else {
    var t_seq := [];  // Use sequence instead of array
    var j := 0;
    while j < |s|
      invariant 0 <= j <= |s|
      invariant |t_seq| == j
      invariant forall k :: 0 <= k < j ==> 
        if is_alpha(s[k]) then t_seq[k] == flip_case(s[k]) else t_seq[k] == s[k]
    {
      if is_alpha(s[j]) {
        t_seq := t_seq + [flip_case(s[j])];
      } else {
        t_seq := t_seq + [s[j]];
      }
      j := j + 1;
    }
    t := t_seq;  // Sequence can be directly assigned to string
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