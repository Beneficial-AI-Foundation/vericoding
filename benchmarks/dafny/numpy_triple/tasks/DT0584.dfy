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
  assume {:axiom} false;
}
// </vc-code>
