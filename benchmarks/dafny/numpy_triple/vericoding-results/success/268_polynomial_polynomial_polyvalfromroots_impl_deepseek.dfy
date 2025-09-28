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
function ComputeResult(n: nat, x: seq<real>, r: seq<real>): seq<real>
  requires n <= |x|
  decreases n
{
  if n == 0 then []
  else [ProductOfDifferences(x[|x| - n], r)] + ComputeResult(n - 1, x, r)
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
  /* code modified by LLM (iteration 2): Fixed ComputeResult call and while loop */
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == ProductOfDifferences(x[j], r)
  {
    result := result + [ProductOfDifferences(x[i], r)];
    i := i + 1;
  }
}
// </vc-code>
