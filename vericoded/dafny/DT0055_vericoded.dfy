// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method flipud(m: seq<real>) returns (result: seq<real>)
    ensures |result| == |m|
    ensures forall i :: 0 <= i < |result| ==> result[i] == m[|m| - 1 - i]
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := |m|;
  while i > 0
    invariant 0 <= i <= |m|
    invariant |result| == |m| - i
    invariant forall j :: 0 <= j < |result| ==> result[j] == m[|m| - 1 - j]
  {
    i := i - 1;
    result := result + [m[i]];
  }
}
// </vc-code>
