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
/* helper modified by LLM (iteration 2): Added method instead of function to avoid timeout */
method FlatIndexToCoordinateMethod(index: nat, shape: seq<nat>) returns (coord: seq<nat>)
    requires |shape| > 0
    requires forall i :: 0 <= i < |shape| ==> shape[i] > 0
    requires index < ProductOfSeq(shape)
    ensures |coord| == |shape|
    ensures ValidCoordinate(coord, shape)
    ensures CoordinateToFlatIndex(coord, shape) == index
{
    if |shape| == 1 {
        coord := [index];
    } else {
        var subProduct := ProductOfSeq(shape[1..]);
        var firstCoord := index / subProduct;
        var remainingIndex := index % subProduct;
        var restCoord := FlatIndexToCoordinateMethod(remainingIndex, shape[1..]);
        coord := [firstCoord] + restCoord;
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
/* code modified by LLM (iteration 2): Updated to use method version of FlatIndexToCoordinate */
{
    coords := [];
    var i := 0;
    while i < |indices|
        invariant 0 <= i <= |indices|
        invariant |coords| == i
        invariant forall j :: 0 <= j < i ==> |coords[j]| == |shape|
        invariant forall j :: 0 <= j < i ==> ValidCoordinate(coords[j], shape)
        invariant forall j :: 0 <= j < i ==> CoordinateToFlatIndex(coords[j], shape) == indices[j]
        invariant forall j, k :: (0 <= j < i && 0 <= k < i && j != k && indices[j] != indices[k]) ==> coords[j] != coords[k]
    {
        var coord := FlatIndexToCoordinateMethod(indices[i], shape);
        coords := coords + [coord];
        i := i + 1;
    }
}
// </vc-code>
