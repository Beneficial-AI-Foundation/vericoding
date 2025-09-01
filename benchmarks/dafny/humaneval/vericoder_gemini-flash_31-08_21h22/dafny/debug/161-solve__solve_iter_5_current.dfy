

// <vc-helpers>
function reverse(s: string) : (rev: string)
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
{
  if |s| == 0 then ""
  else reverse(s[1..]) + s[0..1]
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
    if |s| == 0 then
        t := "";
    else if (forall i :: 0 <= i < |s| ==> !is_alpha(s[i])) then
        t := reverse(s);
    else
        var char_array := new char[|s|];
        for i := 0 to |s| -1
            invariant 0 <= i <= |s|
            invariant forall k :: 0 <= k < i ==>
                (if is_alpha(s[k]) then char_array[k] == flip_case(s[k]) else char_array[k] == s[k])
        {
            if is_alpha(s[i]) then
                char_array[i] := flip_case(s[i]);
            else
                char_array[i] := s[i];
        }
        t := char_array.as_string();
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