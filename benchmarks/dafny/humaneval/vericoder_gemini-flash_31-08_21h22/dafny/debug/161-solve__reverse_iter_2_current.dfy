method solve(s: string) returns (t: string)
  // post-conditions-start 
  ensures |s| == |t|
  ensures (forall i :: 0 <= i < |s| ==> !is_alpha(s[i])) ==> (forall i :: 0 <= i < |s| ==> s[i] == t[|t| - 1 - i])
  ensures (exists i :: 0 <= i < |s| && is_alpha(s[i])) ==> 
    (forall i :: 0 <= i < |t| ==> if is_alpha(s[i]) then t[i] == flip_case(s[i]) else t[i] == s[i])
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function is_alpha(c: char) : bool {
  'a' <= c <= 'z' || 'A' <= c <= 'Z'
}

function flip_case(c: char): (flipped: char)
  requires is_alpha(c)
  ensures is_alpha(flipped)
{
  if 'a' <= c <= 'z' then c - 'a' + 'A' else c - 'A' + 'a'
}

method reverse_string(s: string) returns (rev: string)
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
{
  var a := new char[|s|];
  for k := 0 to |s| - 1
    invariant 0 <= k <= |s|
    invariant forall i :: 0 <= i < k ==> a[i] == s[|s| - 1 - i]
  {
    a[k] := s[|s| - 1 - k];
  }
  rev := new string(a);
}
// </vc-helpers>

// <vc-spec>
method reverse(s: string) returns (rev: string)
  // pre-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // pre-conditions-end
// </vc-spec>
// <vc-code>
{
  var all_non_alpha := true;
  for i := 0 to |s| - 1
    invariant 0 <= i <= |s|
    invariant all_non_alpha ==> (forall j :: 0 <= j < i ==> !is_alpha(s[j]))
  {
    if is_alpha(s[i]) {
      all_non_alpha := false;
    }
  }

  if all_non_alpha {
    t := reverse_string(s);
  } else {
    var a := new char[|s|];
    for i := 0 to |s| - 1
      invariant 0 <= i <= |s|
      invariant forall j :: 0 <= j < i ==> (if is_alpha(s[j]) then a[j] == flip_case(s[j]) else a[j] == s[j])
    {
      if is_alpha(s[i]) {
        a[i] := flip_case(s[i]);
      } else {
        a[i] := s[i];
      }
    }
    t := new string(a);
  }
}
// </vc-code>

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