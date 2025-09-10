

// <vc-helpers>
// No additional helpers required.
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
  var n := |s|;
  var j := 0;
  var hasAlpha := false;
  while j < n
    invariant 0 <= j <= n
    invariant hasAlpha ==> (exists i :: 0 <= i < j && is_alpha(s[i]))
    invariant !hasAlpha ==> (forall i :: 0 <= i < j ==> !is_alpha(s[i]))
  {
    if is_alpha(s[j]) {
      hasAlpha := true;
    }
    j := j + 1;
  }

  if hasAlpha {
    var a := new char[n];
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant forall k :: 0 <= k < i ==> a[k] == (if is_alpha(s[k]) then flip_case(s[k]) else s[k])
    {
      if is_alpha(s[i]) {
        a[i] := flip_case(s[i]);
      } else {
        a[i] := s[i];
      }
      i := i + 1;
    }
    t := new string(a);
  } else {
    var a := new char[n];
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant forall k :: 0 <= k < i ==> a[k] == s[n - 1 - k]
    {
      a[i] := s[n - 1 - i];
      i := i + 1;
    }
    t := new string(a);
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