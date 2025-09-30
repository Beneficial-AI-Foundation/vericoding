// <vc-preamble>
// Multiply two Hermite series represented as coefficient sequences
// The product of Hermite polynomials requires reprojection onto the basis set
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed precondition issues and added zero handling */
function hermiteProduct(c1: seq<real>, c2: seq<real>, k: int): real
  requires |c1| > 0 && |c2| > 0
  requires 0 <= k < |c1| + |c2| - 1
{
  if (forall i :: 0 <= i < |c1| ==> c1[i] == 0.0) || (forall j :: 0 <= j < |c2| ==> c2[j] == 0.0) then
    0.0
  else
    var startI := if k < |c2| then 0 else k - |c2| + 1;
    var endI := if k < |c1| then k else |c1| - 1;
    hermiteProductHelper(c1, c2, k, startI, endI, 0.0)
}

function hermiteProductHelper(c1: seq<real>, c2: seq<real>, k: int, i: int, endI: int, sum: real): real
  requires |c1| > 0 && |c2| > 0
  requires 0 <= k < |c1| + |c2| - 1
  requires 0 <= i <= |c1|
  requires endI < |c1|
  requires i <= endI + 1
  decreases endI + 1 - i
{
  if i > endI then
    sum
  else
    var j := k - i;
    if 0 <= j < |c2| then
      hermiteProductHelper(c1, c2, k, i + 1, endI, sum + c1[i] * c2[j])
    else
      hermiteProductHelper(c1, c2, k, i + 1, endI, sum)
}
// </vc-helpers>

// <vc-spec>
method hermemul(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
  requires |c1| > 0 && |c2| > 0
  ensures |result| == |c1| + |c2| - 1
  // Zero preservation: if either input is all zeros, result is all zeros
  ensures (forall i :: 0 <= i < |c1| ==> c1[i] == 0.0) || 
          (forall j :: 0 <= j < |c2| ==> c2[j] == 0.0) ==> 
          (forall k :: 0 <= k < |result| ==> result[k] == 0.0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Simplified implementation using helper function */
{
  var len := |c1| + |c2| - 1;
  result := seq(len, i requires 0 <= i < len => hermiteProduct(c1, c2, i));
}
// </vc-code>
