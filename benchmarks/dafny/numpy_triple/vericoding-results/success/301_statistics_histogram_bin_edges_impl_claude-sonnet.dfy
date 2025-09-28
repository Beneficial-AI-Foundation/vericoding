// <vc-preamble>
// Helper function to find minimum value in a sequence
function Min(data: seq<real>): real
  requires |data| > 0
{
  if |data| == 1 then data[0]
  else if data[0] <= Min(data[1..]) then data[0]
  else Min(data[1..])
}

// Helper function to find maximum value in a sequence  
function Max(data: seq<real>): real
  requires |data| > 0
{
  if |data| == 1 then data[0]
  else if data[0] >= Max(data[1..]) then data[0]
  else Max(data[1..])
}

// Helper predicate to check if sequence is monotonically increasing
predicate IsMonotonicallyIncreasing(edges: seq<real>)
{
  forall i :: 0 <= i < |edges| - 1 ==> edges[i] < edges[i + 1]
}

// Helper predicate to check if bins have equal width
predicate HasEqualWidthBins(edges: seq<real>)
  requires |edges| >= 2
{
  forall i, j :: 0 <= i < |edges| - 1 && 0 <= j < |edges| - 1 ==>
    edges[i + 1] - edges[i] == edges[j + 1] - edges[j]
}

// Helper predicate to check if all data falls within edge range
predicate DataWithinEdgeRange(data: seq<real>, edges: seq<real>)
  requires |data| > 0 && |edges| >= 2
{
  forall i :: 0 <= i < |data| ==>
    edges[0] <= data[i] <= edges[|edges| - 1]
}
// </vc-preamble>

// <vc-helpers>
// Helper function to compute bin width
function ComputeBinWidth(minVal: real, maxVal: real, numBins: nat): real
  requires numBins > 0
  requires maxVal >= minVal
{
  (maxVal - minVal) / (numBins as real)
}

// Helper function to generate edge at position i
function EdgeAtPosition(minVal: real, binWidth: real, i: nat): real
{
  minVal + (i as real) * binWidth
}

/* helper modified by LLM (iteration 3): fixed lemma with proper bounds */
lemma DataWithinRangeProof(data: seq<real>, minVal: real, maxVal: real, edges: seq<real>)
  requires |data| > 0
  requires minVal == Min(data)
  requires maxVal == Max(data)
  requires |edges| >= 2
  requires edges[0] <= minVal
  requires edges[|edges| - 1] >= maxVal
  requires forall i :: 0 <= i < |data| ==> minVal <= data[i] <= maxVal
  ensures DataWithinEdgeRange(data, edges)
{
  forall i | 0 <= i < |data|
    ensures edges[0] <= data[i] <= edges[|edges| - 1]
  {
    // data[i] is between minVal and maxVal by requirement
    // edges[0] <= minVal <= data[i] <= maxVal <= edges[|edges| - 1]
  }
}

/* helper modified by LLM (iteration 3): added lemma for Min/Max bounds */
lemma MinMaxBounds(data: seq<real>)
  requires |data| > 0
  ensures forall i :: 0 <= i < |data| ==> Min(data) <= data[i] <= Max(data)
{
}

// Lemma to prove edges are monotonically increasing
lemma EdgesMonotonicIncreasing(minVal: real, binWidth: real, numBins: nat, i: nat)
  requires binWidth > 0.0
  requires i < numBins
  ensures EdgeAtPosition(minVal, binWidth, i) < EdgeAtPosition(minVal, binWidth, i + 1)
{
}

// Lemma to prove equal width bins
lemma EdgesEqualWidth(minVal: real, binWidth: real, numBins: nat, i: nat, j: nat)
  requires i < numBins
  requires j < numBins
  ensures EdgeAtPosition(minVal, binWidth, i + 1) - EdgeAtPosition(minVal, binWidth, i) == 
          EdgeAtPosition(minVal, binWidth, j + 1) - EdgeAtPosition(minVal, binWidth, j)
{
}
// </vc-helpers>

// <vc-spec>
method HistogramBinEdges(data: seq<real>, numBins: nat) returns (edges: seq<real>)
  // Input data must be non-empty and number of bins must be positive
  requires |data| > 0
  requires numBins > 0
  
  // Output has correct length: num_bins + 1 edges
  ensures |edges| == numBins + 1
  
  // Edges are monotonically increasing (strictly ordered)
  ensures IsMonotonicallyIncreasing(edges)
  
  // First edge is at or below minimum data value
  ensures edges[0] <= Min(data)
  
  // Last edge is at or above maximum data value  
  ensures edges[|edges| - 1] >= Max(data)
  
  // Bins have equal width (equal spacing between consecutive edges)
  ensures HasEqualWidthBins(edges)
  
  // All data values fall within the range of the edges
  ensures DataWithinEdgeRange(data, edges)
  
  // The bin width is consistent and positive
  ensures numBins > 0 ==> edges[1] - edges[0] > 0.0
  
  // The total range covered by edges spans at least the data range
  ensures edges[|edges| - 1] - edges[0] >= Max(data) - Min(data)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added bounds lemma call */
  var minVal := Min(data);
  var maxVal := Max(data);
  
  // Prove that Min/Max provide proper bounds
  MinMaxBounds(data);
  
  // Extend the range slightly to ensure all data is covered
  var range := maxVal - minVal;
  var epsilon := if range == 0.0 then 1.0 else range * 0.001;
  var adjustedMinVal := minVal - epsilon;
  var adjustedMaxVal := maxVal + epsilon;
  
  var binWidth := ComputeBinWidth(adjustedMinVal, adjustedMaxVal, numBins);
  
  edges := [];
  var i := 0;
  
  while i <= numBins
    invariant 0 <= i <= numBins + 1
    invariant |edges| == i
    invariant forall k :: 0 <= k < i ==> edges[k] == EdgeAtPosition(adjustedMinVal, binWidth, k)
    invariant i > 1 ==> forall k :: 0 <= k < i - 1 ==> edges[k] < edges[k + 1]
  {
    var edge := EdgeAtPosition(adjustedMinVal, binWidth, i);
    edges := edges + [edge];
    
    if i > 0 {
      EdgesMonotonicIncreasing(adjustedMinVal, binWidth, numBins, i - 1);
    }
    
    i := i + 1;
  }
  
  // Prove equal width property
  forall i, j | 0 <= i < numBins && 0 <= j < numBins {
    EdgesEqualWidth(adjustedMinVal, binWidth, numBins, i, j);
  }
  
  // Prove data within range
  DataWithinRangeProof(data, minVal, maxVal, edges);
}
// </vc-code>
