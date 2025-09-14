// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ElementWiseModulo(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    requires |a| > 0
    requires forall i :: 0 <= i < |b| ==> b[i] != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] % b[i]
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := [];
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] % b[k]
  {
    var mod_val := a[i] % b[i];
    result := result + [mod_val];
    i := i + 1;
  }
}
// </vc-code>
