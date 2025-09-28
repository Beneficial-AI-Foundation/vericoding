// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function reverse<T>(s: seq<T>): seq<T>
  ensures |reverse(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> reverse(s)[i] == s[|s| - 1 - i]
{
  if |s| == 0 then []
  else reverse(s[1..]) + [s[0]]
}

// </vc-helpers>

// <vc-spec>
method flipud(m: seq<real>) returns (result: seq<real>)
    ensures |result| == |m|
    ensures forall i :: 0 <= i < |result| ==> result[i] == m[|m| - 1 - i]
// </vc-spec>
// <vc-code>
{
  result := reverse(m);
}
// </vc-code>
