// <vc-preamble>
// Helper function to compute the product of all elements in a sequence
function ProductOfSeq(s: seq<nat>): nat
{
    if |s| == 0 then 1
    else s[0] * ProductOfSeq(s[1..])
}

// Helper function to convert multi-dimensional coordinates back to flat index
function CoordinateToFlatIndex(coord: seq<nat>, shape: seq<nat>): nat
    requires |coord| == |shape|
    requires |shape| > 0
{
    if |coord| == 1 then coord[0]
    else coord[0] * ProductOfSeq(shape[1..]) + CoordinateToFlatIndex(coord[1..], shape[1..])
}

// Helper function to check if a coordinate is valid for the given shape
predicate ValidCoordinate(coord: seq<nat>, shape: seq<nat>)
{
    |coord| == |shape| &&
    forall j :: 0 <= j < |coord| ==> coord[j] < shape[j]
}

// Main method that converts flat indices to multi-dimensional coordinates
// </vc-preamble>

// <vc-helpers>
function UnravelSingleIndex(idx: nat, shape: seq<nat>): seq<nat>
    requires 0 <= idx < ProductOfSeq(shape)
    requires |shape| > 0
    decreases |shape|
    ensures |UnravelSingleIndex(idx, shape)| == |shape|
    ensures ValidCoordinate(UnravelSingleIndex(idx, shape), shape)
    ensures CoordinateToFlatIndex(UnravelSingleIndex(idx, shape), shape) == idx
{
    if |shape| == 1 then [idx]
    else
        var product_rest := ProductOfSeq(shape[1..]);
        var d0 := idx / product_rest;
        var idx_rest := idx % product_rest;
        [d0] + UnravelSingleIndex(idx_rest, shape[1..])
}
// </vc-helpers>

// <vc-spec>
method UnravelIndex(indices: seq<nat>, shape: seq<nat>) returns (coords: seq<seq<nat>>)
    // Shape must be non-empty and all dimensions must be positive
    requires |shape| > 0
    requires forall i :: 0 <= i < |shape| ==> shape[i] > 0
    // All indices must be valid flat indices for the given shape
    requires forall i :: 0 <= i < |indices| ==> indices[i] < ProductOfSeq(shape)
    
    // Output has same length as input indices
    ensures |coords| == |indices|
    // Each coordinate has the same dimensionality as the shape
    ensures forall i :: 0 <= i < |coords| ==> |coords[i]| == |shape|
    // Each coordinate component is within bounds for its dimension
    ensures forall i :: 0 <= i < |coords| ==> ValidCoordinate(coords[i], shape)
    // Uniqueness: different flat indices produce different coordinates
    ensures forall i, j :: (0 <= i < |indices| && 0 <= j < |indices| && 
                          i != j && indices[i] != indices[j]) ==> 
                          coords[i] != coords[j]
    // Correctness: each coordinate correctly represents its corresponding flat index
    ensures forall i :: 0 <= i < |coords| ==> CoordinateToFlatIndex(coords[i], shape) == indices[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added loop invariants to prove postconditions */
  var resultCoords := [];
  for i := 0 to |indices|
      invariant |resultCoords| == i
      invariant forall j :: 0 <= j < i ==> |resultCoords[j]| == |shape|
      invariant forall j :: 0 <= j < i ==> ValidCoordinate(resultCoords[j], shape)
      invariant forall j :: 0 <= j < i ==> CoordinateToFlatIndex(resultCoords[j], shape) == indices[j]
      invariant forall j, k :: 0 <= j < k < i ==> (resultCoords[j] == resultCoords[k] ==> indices[j] == indices[k])
  {
      resultCoords := resultCoords + [UnravelSingleIndex(indices[i], shape)];
  }
  return resultCoords;
}
// </vc-code>
