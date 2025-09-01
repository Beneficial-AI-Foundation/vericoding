

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
  var hasAlpha := false;
  var i := 0;
  while i < |s| && !hasAlpha
    invariant 0 <= i <= |s|
    invariant !hasAlpha ==> forall j :: 0 <= j < i ==> !is_alpha(s[j])
  {
    if is_alpha(s[i]) {
      hasAlpha := true;
    }
    i := i + 1;
  }

  if !hasAlpha {
    var t := "";
    for j := |s| - 1 downto 0
      invariant |t| == |s| - 1 - j
      invariant forall m :: 0 <= m < |t| ==> t[m] == s[|s|-1-m]
    {
      t := t + s[j].ToString();
    }
    return t;
  } else {
    var t := "";
    for j := 0 to |s|
      invariant |t| == j
      invariant forall k :: 0 <= k < j ==> 
        (if is_alpha(s[k]) then t[k] == flip_case(s[k]) else t[k] == s[k])
    {
      if is_alpha(s[j]) then
        t := t + flip_case(s[j]).ToString()
      else
        t := t + s[j].ToString();
    }
    return t;
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