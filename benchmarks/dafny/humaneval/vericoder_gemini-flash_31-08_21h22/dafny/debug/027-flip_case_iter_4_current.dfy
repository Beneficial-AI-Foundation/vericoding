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
  ensures (lower(c) && upper(C) && C == (c as int - 'a' as int + 'A' as int)as char) || (upper(c) && lower(C) && C == (c as int + 'a' as int - 'A' as int)as char) || (!alpha(c) && C == c)
{
  if lower(c) then (c as int - 'a' as int + 'A' as int)as char
  else if upper(c) then (c as int + 'a' as int - 'A' as int)as char
  else c
}

function method CharArrayToString(a: array<char>) : string
  reads a
  requires a != null
  ensures |CharArrayToString(a)| == a.Length
{
  var s := "";
  for i := 0 to a.Length - 1
    invariant 0 <= i <= a.Length
    invariant |s| == i
    invariant forall k :: 0 <= k < i ==> s[k] == a[k]
  {
    s := s + a[i];
  }
  return s;
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
    S_array[i] := flip_char_helper(s[i]);
  }
  return CharArrayToString(S_array);
}
// </vc-code>

