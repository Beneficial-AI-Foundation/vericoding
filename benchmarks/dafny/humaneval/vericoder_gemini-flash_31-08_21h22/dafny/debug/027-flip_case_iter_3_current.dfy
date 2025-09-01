function lower(c: char) : bool
    {
        'a' <= c <= 'z'
    }
function upper(c: char) : bool
    {
        'A' <= c <= 'Z'
    }
function alpha(c: char) : bool
    {
        lower(c) || upper(c)
    }
function flip_char(c: char) : (C: char)
        ensures lower(c) <==> upper(C)
        ensures upper(c) <==> lower(C)
    {
        if lower(c) then c - 'a' + 'A' else
        if upper(c) then c + 'a' - 'A' else c
    }

// <vc-helpers>
function flip_char_helper(c: char) : (C: char)
  ensures (lower(c) && upper(C)) || (upper(c) && lower(C)) || (!alpha(c) && C == c)
{
  if lower(c) then (c - 'a' + 'A')
  else if upper(c) then (c + 'a' - 'A')
  else c
}
// </vc-helpers>

// <vc-spec>
method flip_case(s: string) returns (S: string)
    // post-conditions-start
    ensures |S| == |s|
    ensures forall i :: 0 <= i < |s| ==> (lower(s[i]) <==> upper(S[i]))
    ensures forall i :: 0 <= i < |s| ==> (upper(s[i]) <==> lower(S[i]))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var S_array := new char[|s|];
  for i := 0 to |s| - 1
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> (lower(s[j]) <==> upper(S_array[j]))
    invariant forall j :: 0 <= j < i ==> (upper(s[j]) <==> lower(S_array[j]))
    invariant forall j :: 0 <= j < i ==> (!alpha(s[j]) ==> S_array[j] == s[j])
  {
    S_array[i] := flip_char(s[i]);
  }
  return S_array as string;
}
// </vc-code>

