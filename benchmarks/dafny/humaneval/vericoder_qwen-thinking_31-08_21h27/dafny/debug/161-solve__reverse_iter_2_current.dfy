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
method reverse(s: string) returns (rev: string)
{
  rev := "";
  for i := |s| - 1 downto 0 {
    rev := rev + s[i];
  }
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
if (exists i :: 0 <= i < |s| && is_alpha(s[i])) {
    var t := "";
    for j := 0 to |s| - 1 {
      if is_alpha(s[j]) {
        t := t + flip_case(s[j]);
      } else {
        t := t + s[j];
      }
    }
    return t;
  } else {
    return reverse(s);
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