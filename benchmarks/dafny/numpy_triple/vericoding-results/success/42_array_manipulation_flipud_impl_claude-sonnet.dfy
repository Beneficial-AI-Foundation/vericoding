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
  var i := 0;
  while i < |m|
    invariant 0 <= i <= |m|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == m[|m| - 1 - j]
  {
    result := result + [m[|m| - 1 - i]];
    i := i + 1;
  }
}
// </vc-code>
