// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ToArray(xs: seq<int>) returns (result: array<int>)
    ensures
        result.Length == |xs| &&
        forall i :: 0 <= i < |xs| ==> result[i] == xs[i]
// </vc-spec>
// <vc-code>
{
  result := new int[|xs|];
  var i := 0;
  while i < |xs|
    invariant 0 <= i <= |xs|
    invariant forall j :: 0 <= j < i ==> result[j] == xs[j]
  {
    result[i] := xs[i];
    i := i + 1;
  }
}
// </vc-code>
