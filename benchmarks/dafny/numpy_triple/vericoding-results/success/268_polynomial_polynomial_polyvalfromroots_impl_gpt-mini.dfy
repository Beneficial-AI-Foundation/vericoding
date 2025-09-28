// <vc-preamble>
// Helper function to compute the product of (point - roots[j]) for all j in [0, |roots|)
function ProductOfDifferences(point: real, roots: seq<real>): real
{
  ProductOfDifferencesHelper(point, roots, 0)
}

function ProductOfDifferencesHelper(point: real, roots: seq<real>, index: nat): real
  requires 0 <= index <= |roots|
  decreases |roots| - index
{
  if index == |roots| then 1.0
  else (point - roots[index]) * ProductOfDifferencesHelper(point, roots, index + 1)
}

// Main method: evaluates polynomial with given roots at each point in x
// </vc-preamble>

// <vc-helpers>
lemma ProductOfDifferences_unfold(point: real, roots: seq<real>)
  ensures ProductOfDifferences(point, roots) == ProductOfDifferencesHelper(point, roots, 0)
{
}

// </vc-helpers>

// <vc-spec>
method polyvalfromroots(x: seq<real>, r: seq<real>) returns (result: seq<real>)
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |x| ==> 
    result[i] == ProductOfDifferences(x[i], r)
// </vc-spec>
// <vc-code>
{
  var n := |x|;
  var arr := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> arr[j] == ProductOfDifferences(x[j], r)
  {
    arr[i] := ProductOfDifferences(x[i], r);
    i := i + 1;
  }
  result := arr[..];
}
// </vc-code>
