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
  var i := 0;
  S := s;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |S| == |s|
    invariant forall j :: 0 <= j < i ==> (lower(s[j]) <==> upper(S[j]))
    invariant forall j :: 0 <= j < i ==> (upper(s[j]) <==> lower(S[j]))
    invariant forall j :: i <= j < |s| ==> S[j] == s[j]
  {
    S := S[..i] + [flip_char(s[i])] + S[i+1..];
    i := i + 1;
  }
}
// </vc-code>

