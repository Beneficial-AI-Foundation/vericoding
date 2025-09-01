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
  var result: seq<char> := [];
  for i : int := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> (lower(s[k]) <==> upper(result[k]))
    invariant forall k :: 0 <= k < i ==> (upper(s[k]) <==> lower(result[k]))
  {
    result := result + [flip_char(s[i])];
  }
  S := result;
}
// </vc-code>

