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
/* helper modified by LLM (iteration 4): removed 'then' keyword to fix a compilation syntax error. */
method FlatIndexToCoordinate(index: nat, shape: seq<nat>) returns (coord: seq<nat>)
  requires |shape| > 0
  requires forall i :: 0 <= i < |shape| ==> shape[i] > 0
  requires index < ProductOfSeq(shape)
  ensures |coord| == |shape|
  ensures ValidCoordinate(coord, shape)
  ensures CoordinateToFlatIndex(coord, shape) == index
  decreases |shape|
{
  if |shape| == 1
  {
    assert ProductOfSeq(shape) == shape[0];
    coord := [index];
  }
  else
  {
    var stride := ProductOfSeq(shape[1..]);
    var c0 := index / stride;
    var rem_index := index % stride;
    var sub_coord := FlatIndexToCoordinate(rem_index, shape[1..]);
    coord := [c0] + sub_coord;
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
  /* code modified by LLM (iteration 4): no change in logic, only fixing helper syntax. */
  coords := [];
  var i: nat := 0;
  while i < |indices|
    invariant |coords| == i
    invariant i <= |indices|
    invariant forall k :: 0 <= k < |coords| ==> |coords[k]| == |shape|
    invariant forall k :: 0 <= k < |coords| ==> ValidCoordinate(coords[k], shape)
    invariant forall k :: 0 <= k < |coords| ==> CoordinateToFlatIndex(coords[k], shape) == indices[k]
    decreases |indices| - i
  {
    var new_coord := FlatIndexToCoordinate(indices[i], shape);
    coords := coords + [new_coord];
    i := i + 1;
  }
}
// </vc-code>
