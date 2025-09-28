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
/* helper modified by LLM (iteration 5): Fixed compilation error by removing `var` from `while` loop condition. */
function GenerateBinEdges(min_val: real, max_val: real, n_bins: nat): seq<real>
    requires n_bins > 0
    requires min_val < max_val
    ensures |result| == n_bins + 1
    ensures result[0] == min_val
    ensures result[n_bins] == max_val
    ensures MonotonicallyIncreasing(result)
    ensures UniformBinWidths(result, n_bins, min_val, max_val)
{
    var bin_width := (max_val - min_val) / (n_bins as real);
    var edges: seq<real> := [min_val];
    var i := 1;
    while i <= n_bins
        invariant 0 <= i <= n_bins + 1
        invariant |edges| == i
        invariant edges[0] == min_val
        invariant forall k :: 0 <= k < i ==> edges[k] == min_val + (k as real) * bin_width
    {
        edges := edges + [min_val + (i as real) * bin_width];
        i := i + 1;
    }
    return edges;
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
/* code modified by LLM (iteration 5): Removed redundant variable declaration `var idx` which was causing a parse error. The `idx` variable was already declared. */
{
    var bin_edges_arr: array<real> := new real[n_bins + 1];
    var bin_width := (max_val - min_val) / (n_bins as real);

    bin_edges_arr[0] := min_val;
    var i := 1;
    while i <= n_bins
        invariant 0 <= i <= n_bins + 1
        invariant bin_edges_arr.Length == n_bins + 1
        invariant bin_edges_arr[0] == min_val
        invariant forall k :: 0 <= k < i ==> bin_edges_arr[k] == min_val + (k as real) * bin_width
    {
        bin_edges_arr[i] := min_val + (i as real) * bin_width;
        i := i + 1;
    }
    var bin_edges := bin_edges_arr.seq;

    var counts_arr: array<nat> := new nat[n_bins];

    i := 0;
    while i < n_bins
        invariant 0 <= i <= n_bins
        invariant counts_arr.Length == n_bins
        invariant bin_edges.Length == n_bins + 1
        invariant forall k :: 0 <= k < i ==> counts_arr[k] == CountInBinCorrect(data, k, bin_edges)
    {
        counts_arr[i] := CountInBinCorrect(data, i, bin_edges);
        i := i + 1;
    }
    var counts := counts_arr.seq;

    // Verify SumCounts property
    var total_count := 0;
    var idx := 0;
    while idx < n_bins
        invariant 0 <= idx <= n_bins
        invariant total_count == SumCounts(counts[0..idx])
    {
        total_count := total_count + counts[idx];
        idx := idx + 1;
    }
    
    return HistogramResult(counts, bin_edges);
}
// </vc-code>
