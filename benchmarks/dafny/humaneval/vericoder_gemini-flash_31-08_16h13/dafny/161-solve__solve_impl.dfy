

// <vc-helpers>
function reverse_string(s: string) : string
  ensures |reverse_string(s)| == |s|
  ensures forall k :: 0 <= k < |s| ==> reverse_string(s)[k] == s[|s| - 1 - k]
{
  if |s| == 0 then ""
  else (new string(s[|s|-1..]) + reverse_string(s[..|s|-1]))
}

function is_alpha_char(c: char) : bool {
  'a' <= c <= 'z' || 'A' <= c <= 'Z'
}

function flip_case_char(c: char): (flipped: char)
  requires is_alpha_char(c)
  ensures is_alpha_char(flipped)
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
    invariant 0 <= i <= |s|
    invariant has_alpha ==> (exists k :: 0 <= k < i && is_alpha_char(s[k]))
  {
    if is_alpha_char(s[i]) {
      has_alpha := true;
      break;
    }
  }

  if has_alpha {
    var char_array := new char[|s|];
    for i := 0 to |s| - 1
      invariant 0 <= i <= |s|
      invariant forall k :: 0 <= k < i ==>
        (if is_alpha_char(s[k]) then char_array[k] == flip_case_char(s[k]) else char_array[k] == s[k])
    {
      if is_alpha_char(s[i]) {
        char_array[i] := flip_case_char(s[i]);
      } else {
        char_array[i] := s[i];
      }
    }
    t := new string(char_array);
  } else {
    t := reverse_string(s);
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