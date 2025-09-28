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
/* helper modified by LLM (iteration 5): Simplified FlatIndexToCoordinate function with reduced complexity */
function FlatIndexToCoordinate(index: nat, shape: seq<nat>): seq<nat>
    requires |shape| > 0
    requires forall i :: 0 <= i < |shape| ==> shape[i] > 0
    requires index < ProductOfSeq(shape)
    ensures |FlatIndexToCoordinate(index, shape)| == |shape|
    decreases |shape|
{
    if |shape| == 1 then
        [index]
    else 
        var stride := ProductOfSeq(shape[1..]);
        var quotient := index / stride;
        var remainder := index % stride;
        [quotient] + FlatIndexToCoordinate(remainder, shape[1..])
}

lemma FlatIndexToCoordinateValid(index: nat, shape: seq<nat>)
    requires |shape| > 0
    requires forall i :: 0 <= i < |shape| ==> shape[i] > 0
    requires index < ProductOfSeq(shape)
    ensures ValidCoordinate(FlatIndexToCoordinate(index, shape), shape)
    decreases |shape|
{
    var coord := FlatIndexToCoordinate(index, shape);
    if |shape| == 1 {
        assert coord == [index];
        assert index < shape[0];
    } else {
        var stride := ProductOfSeq(shape[1..]);
        var quotient := index / stride;
        var remainder := index % stride;
        assert quotient < shape[0] by {
            assert index < ProductOfSeq(shape);
            assert ProductOfSeq(shape) == shape[0] * stride;
        }
        FlatIndexToCoordinateValid(remainder, shape[1..]);
    }
}

lemma FlatIndexInverse(index: nat, shape: seq<nat>)
    requires |shape| > 0
    requires forall i :: 0 <= i < |shape| ==> shape[i] > 0
    requires index < ProductOfSeq(shape)
    ensures CoordinateToFlatIndex(FlatIndexToCoordinate(index, shape), shape) == index
    decreases |shape|
{
    if |shape| == 1 {
        assert FlatIndexToCoordinate(index, shape) == [index];
    } else {
        var stride := ProductOfSeq(shape[1..]);
        var quotient := index / stride;
        var remainder := index % stride;
        FlatIndexInverse(remainder, shape[1..]);
    }
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
  /* code modified by LLM (iteration 5): Simplified implementation using helper lemmas */
  coords := [];
  var i := 0;
  while i < |indices|
    invariant 0 <= i <= |indices|
    invariant |coords| == i
    invariant forall k :: 0 <= k < i ==> |coords[k]| == |shape|
    invariant forall k :: 0 <= k < i ==> ValidCoordinate(coords[k], shape)
    invariant forall k :: 0 <= k < i ==> CoordinateToFlatIndex(coords[k], shape) == indices[k]
  {
    var coord := FlatIndexToCoordinate(indices[i], shape);
    FlatIndexToCoordinateValid(indices[i], shape);
    FlatIndexInverse(indices[i], shape);
    coords := coords + [coord];
    i := i + 1;
  }
}
// </vc-code>
