// <vc-preamble>
// Constructs a 2x2 block matrix from four equal-sized vectors and returns the flattened result
// </vc-preamble>

// <vc-helpers>
function Flatten(s1: seq<real>, s2: seq<real>, s3: seq<real>, s4: seq<real>): seq<real>
{
  s1 + s2 + s3 + s4
}
// </vc-helpers>

// <vc-spec>
method bmat(topLeft: seq<real>, topRight: seq<real>, bottomLeft: seq<real>, bottomRight: seq<real>) 
    returns (result: seq<real>)
    // All input vectors must have the same length
    requires |topLeft| == |topRight|
    requires |topLeft| == |bottomLeft| 
    requires |topLeft| == |bottomRight|
    // Result has length 4 times the input vector length
    ensures |result| == 4 * |topLeft|
    // First block: elements 0 to n-1 come from topLeft
    ensures forall i :: 0 <= i < |topLeft| ==> result[i] == topLeft[i]
    // Second block: elements n to 2n-1 come from topRight
    ensures forall i :: 0 <= i < |topRight| ==> result[i + |topLeft|] == topRight[i]
    // Third block: elements 2n to 3n-1 come from bottomLeft
    ensures forall i :: 0 <= i < |bottomLeft| ==> result[i + 2 * |topLeft|] == bottomLeft[i]
    // Fourth block: elements 3n to 4n-1 come from bottomRight
    ensures forall i :: 0 <= i < |bottomRight| ==> result[i + 3 * |topLeft|] == bottomRight[i]
// </vc-spec>
// <vc-code>
{
  var n := |topLeft|;
  result := Flatten(topLeft, topRight, bottomLeft, bottomRight);
}
// </vc-code>
