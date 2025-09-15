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

// </vc-helpers>

// <vc-spec>
method flip_case(s: string) returns (S: string)

    ensures |S| == |s|
    ensures forall i :: 0 <= i < |s| ==> (lower(s[i]) <==> upper(S[i]))
    ensures forall i :: 0 <= i < |s| ==> (upper(s[i]) <==> lower(S[i]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added loop with invariants to prove length and flipping postconditions */
  var result := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> (lower(s[j]) <==> upper((result)[j]))
    invariant forall j :: 0 <= j < i ==> (upper(s[j]) <==> lower((result)[j]))
  {
    result := result + [flip_char(s[i])];
    i := i + 1;
  }
  S := result;
}
// </vc-code>
