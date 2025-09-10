method solve(s: string) returns (t: string)
  // post-conditions-start 
  ensures |s| == |t|
  ensures (forall i :: 0 <= i < |s| ==> !is_alpha(s[i])) ==> (forall i :: 0 <= i < |s| ==> s[i] == t[|t| - 1 - i])
  ensures (exists i :: 0 <= i < |s| && is_alpha(s[i])) ==> 
    (forall i :: 0 <= i < |t| ==> if is_alpha(s[i]) then t[i] == flip_case(s[i]) else t[i] == s[i])
  // post-conditions-end
{
  // impl-start
  var flag := false;
  t := "";

  var i := 0;
  while i < |s|
    // invariants-start
    invariant 0 <= i <= |s|
    invariant |t| == i
    invariant flag <==> exists j :: 0 <= j < i && is_alpha(s[j])
    invariant forall j :: 0 <= j < i ==> t[j] == if is_alpha(s[j]) then flip_case(s[j]) else s[j]
    // invariants-end
  {
    if is_alpha(s[i]) {
      t := t + [flip_case(s[i])];
      flag := true;
    } else {
      t := t + [s[i]];
    }
    i := i + 1;
  }

  if !flag {
    t := reverse(t);
  }
  // impl-end
}

method reverse(s: string) returns (rev: string)
  // pre-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // pre-conditions-end
{
  // impl-start
  rev := "";
  var i := 0;
  while (i < |s|)
    // invariants-start
    invariant i >= 0 && i <= |s|
    invariant |rev| == i
    invariant forall k :: 0 <= k < i ==> rev[k] == s[|s| - 1 - k]
    // invariants-end
  {
    rev := rev + [s[|s| - i - 1]];
    i := i + 1;
  }
  // impl-end
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
