// <vc-preamble>
datatype HistogramResult = HistogramResult(counts: seq<nat>, bin_edges: seq<real>)

predicate InRange(x: real, min_val: real, max_val: real)
{
    min_val <= x <= max_val
}

predicate MonotonicallyIncreasing(edges: seq<real>)
{
    forall i, j :: 0 <= i < j < |edges| ==> edges[i] < edges[j]
}

predicate UniformBinWidths(edges: seq<real>, n_bins: nat, min_val: real, max_val: real)
    requires |edges| == n_bins + 1
    requires n_bins > 0
{
    var expected_width := (max_val - min_val) / (n_bins as real);
    forall i :: 0 <= i < n_bins ==> edges[i+1] - edges[i] == expected_width
}

function CountInBin(data: seq<real>, left_edge: real, right_edge: real): nat
{
    |set i | 0 <= i < |data| && left_edge <= data[i] < right_edge|
}

function CountInBinCorrect(data: seq<real>, bin_index: nat, edges: seq<real>): nat
    requires bin_index < |edges| - 1
    requires |edges| >= 2
{
    var left_edge := edges[bin_index];
    var right_edge := edges[bin_index + 1];
    if bin_index == |edges| - 2 then
        // Rightmost bin: inclusive on both ends
        |set i | 0 <= i < |data| && left_edge <= data[i] <= right_edge|
    else
        // Other bins: left-inclusive, right-exclusive
        |set i | 0 <= i < |data| && left_edge <= data[i] < right_edge|
}

function CountInRange(data: seq<real>, min_val: real, max_val: real): nat
{
    |set i | 0 <= i < |data| && InRange(data[i], min_val, max_val)|
}

function SumCounts(counts: seq<nat>): nat
{
    if |counts| == 0 then 0
    else counts[0] + SumCounts(counts[1..])
}
// </vc-preamble>

// <vc-helpers>
function ComputeBinEdges(n_bins: nat, min_val: real, max_val: real): seq<real>
  requires n_bins > 0
  ensures |result| == n_bins + 1
  ensures MonotonicallyIncreasing(result)
  ensures result[0] == min_val
  ensures result[n_bins] == max_val
  ensures UniformBinWidths(result, n_bins, min_val, max_val)
{
  /* helper modified by LLM (iteration 4): Replaced seq comprehension with recursive function to avoid compilation error */
  var width := (max_val - min_val) / (n_bins as real);
  ComputeEdgesRec(n_bins, min_val, width)
}

function ComputeEdgesRec(n: nat, current: real, width: real): seq<real>
  ensures |result| == n + 1
  ensures result[0] == current
  ensures forall i :: 0 <= i < |result| - 1 ==> result[i+1] == result[i] + width
{
  if n == 0 then [current]
  else [current] + ComputeEdgesRec(n-1, current + width, width)
}

function ComputeCounts(data: seq<real>, edges: seq<real>): seq<nat>
  requires |edges| >= 2
  ensures |result| == |edges| - 1
  ensures forall i :: 0 <= i < |result| ==> result[i] == CountInBinCorrect(data, i, edges)
{
  /* helper modified by LLM (iteration 5): Replaced seq comprehension with recursive function to avoid compilation error */
  ComputeCountsRec(data, edges, 0)
}

function ComputeCountsRec(data: seq<real>, edges: seq<real>, current: nat): seq<nat>
  decreases |edges| - 1 - current
  requires 0 <= current < |edges| - 1
  requires |edges| >= 2
  ensures |result| == (|edges| - 1 - current)
  ensures forall i :: 0 <= i < |result| ==> result[i] == CountInBinCorrect(data, current + i, edges)
{
  if current == |edges| - 2 then [CountInBinCorrect(data, current, edges)]
  else CountInBinCorrect(data, current, edges) + ComputeCountsRec(data, edges, current + 1)
}
// </vc-helpers>

// <vc-spec>
method Histogram(data: seq<real>, min_val: real, max_val: real, n_bins: nat) returns (result: HistogramResult)
    requires n_bins > 0
    requires min_val < max_val
    ensures |result.counts| == n_bins
    ensures |result.bin_edges| == n_bins + 1
    // Bin edges are monotonically increasing
    ensures MonotonicallyIncreasing(result.bin_edges)
    // Boundary conditions: first edge is min_val, last edge is max_val
    ensures result.bin_edges[0] == min_val
    ensures result.bin_edges[n_bins] == max_val
    // Uniform binning: all bin widths are equal
    ensures UniformBinWidths(result.bin_edges, n_bins, min_val, max_val)
    // Each bin count matches the actual number of data points in that bin
    ensures forall i :: 0 <= i < n_bins ==>
        result.counts[i] == CountInBinCorrect(data, i, result.bin_edges)
    // Conservation: total count equals number of data points in range
    ensures SumCounts(result.counts) == CountInRange(data, min_val, max_val)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Implemented histogram computation by constructing histogram result using helper functions */
  result := HistogramResult(ComputeCounts(data, ComputeBinEdges(n_bins, min_val, max_val)), ComputeBinEdges(n_bins, min_val, max_val));
}
// </vc-code>
