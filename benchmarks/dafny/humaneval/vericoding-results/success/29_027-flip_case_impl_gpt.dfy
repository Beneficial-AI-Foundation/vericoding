// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
function flip_seq(xs: seq<char>) : seq<char>
  decreases |xs|
{
  if |xs| == 0 then [] else [flip_char(xs[0])] + flip_seq(xs[1..])
}
// </vc-helpers>

// <vc-spec>
method flip_case(s: string) returns (S: string)

    ensures |S| == |s|
    ensures forall i :: 0 <= i < |s| ==> (lower(s[i]) <==> upper(S[i]))
    ensures forall i :: 0 <= i < |s| ==> (upper(s[i]) <==> lower(S[i]))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  S := [];
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |S| == i
    invariant forall k :: 0 <= k < i ==> (lower(s[k]) <==> upper(S[k]))
    invariant forall k :: 0 <= k < i ==> (upper(s[k]) <==> lower(S[k]))
    decreases |s| - i
  {
    S := S + [flip_char(s[i])];
    i := i + 1;
  }
}
// </vc-code>
